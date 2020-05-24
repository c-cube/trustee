
require "colorize"
require "json"
require "http/client"
require "option_parser"
require "uri"
require "path"
require "dir"
require "file"
require "io"

require "myhtml" # parse web pages
require "crystar" # parse tar files

Root = "http://opentheory.gilith.com/"

class Semaphore
  def initialize(n : Int32)
    raise Exception.new "semaphore needs positive argument, not #{n}" unless n > 0
    @wait = Channel(Nil).new n
    n.times { @wait.send(nil) }
  end

  def acquire(&block)
    @wait.receive
    begin
      yield
    ensure
      @wait.send nil
    end
  end
end

class URI
  def with_path(p : String) : URI
    uri2 = self.dup
    uri2.path = p
    uri2 = uri2.normalize
    return uri2
  end
end

class Package
  include JSON::Serializable

  property name : String
  property uri : URI
  property version : String?
  property deps : Array(Package)?
  property tar : String?

  def initialize(@name, @uri)
  end

  def fetch()
    return if @version != nil

    puts "fetch pkg `#{@name}` at uri #{@uri}"
    res = HTTP::Client.get @uri
    if res.status_code != 200
      raise Exception.new "could not access package #{@name}: #{res.inspect}"
    end

    html = Myhtml::Parser.new res.body
    html.css("a").each do |p|
      if p.inner_text == "package document"
        local_href = p.attribute_by("href")
        if local_href.nil?
          raise Exception.new "no href found"
        end
        uri2 = @uri.with_path local_href
        fetch_pkg_tar uri2
        break
      end
    end
  end

  def fetch_pkg_tar(uri2 : URI)
    puts "look for content at #{uri2}"
    res = HTTP::Client.get uri2.to_s
    puts "response for `#{@name}` at `#{uri2}`: #{res.status_code}"

    html = Myhtml::Parser.new res.body
    html.css("a").each do |p|
      if p.inner_text.ends_with? ".tgz"
        href = p.attribute_by("href")
        raise Exception.new "no href" if href.nil?

        puts "uri3: use #{href}"
        path = Path.new(uri2.path).parent / href
        uri3 = uri2.with_path path.to_s
        puts "uri3 for `#{name}`: #{uri3}"
        HTTP::Client.get uri3.to_s do |resp|
          puts "got tar: #{resp.status_code}, size=#{resp.body.size}, #{resp.headers}"
          return unless resp.status_code == 200
          # save file
          tar_file = "dl/" + path.to_s
          @tar = tar_file
          Dir.mkdir_p ("dl/" + path.dirname)
          puts "save to file #{tar_file}..."
          File.open(tar_file, mode: "w") do |file|
            IO.copy resp.body_io, file
          end
        end
      end
    end
  end
end

class PackageList
  property pkgs = Hash(String, Package).new

  def to_s (io : IO)
    io.puts "pkg_l (#{pkgs.size} packages)"
  end

  # Download list of packages
  def initialize()
    puts "#{"downloading list of packages".colorize(:green)}…"
    url0 = URI.parse "#{Root}/packages/"
    res = HTTP::Client.get url0
    if res.status_code != 200
      raise Exception.new "could not access list of packages: #{res.inspect}"
    end

    # find packages in the list
    html = Myhtml::Parser.new res.body
    html.css("a.package").each do |p|
      name = p.inner_text
      uri = url0.dup
      local_href = p.attribute_by("href")
      if local_href.nil?
        raise Exception.new "no link for package #{name}"
      end
      uri.path = uri.path + local_href
      uri = uri.normalize
      puts "got package name: #{name}, uri: #{uri}"
      pkg = Package.new(name, uri)
      @pkgs[name] = pkg
    end
    self
  end

  def fetch_all(j : Int32 = 8)
    c = Channel(Nil).new
    sem = Semaphore.new j
    @pkgs.each do |_, pkg|
      spawn do
        begin
          sem.acquire do
            pkg.fetch()
          end
        ensure
          c.send nil
        end
      end
    end
    # wait for all tasks to be done
    @pkgs.size.times {|_| c.receive}
  end
end

def main()
  j = 8
  OptionParser.parse do |p|
    p.banner = "Usage: opentheory-dl [option*]"
    p.on("-j JOBS", "number of jobs") { |x| j = x.to_i32 }
    p.on("-h", "--help", "Show this help") { puts p; exit 0 }
  end
  pkg_l = PackageList.new
  puts "#{"got pkg list".colorize(:green)}: #{ pkg_l }"
  puts "fetching individual packages…"
  pkg_l.fetch_all(j: j)
  puts "done fetching packages!"
end

main()
