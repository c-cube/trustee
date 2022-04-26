
let top = parse_top_str ~filename:"t1"
{|fn f(x,y) {
   f(x,y) }
|};;

Format.printf "parsed:@ %a@." (pp_or_error Ast.pp_top) top;;

let top = parse_top_str ~filename:"t1"
{|fn f(x,y) {
  let z1 = f(g(h(x), y), z1, z2);
  g(z1, z1);
  z1
}

f(1, "yolo");

fn g(x) { x }
|};;

Format.printf "parsed:@ %a@." (pp_or_error Ast.pp_top) top;;

let top = parse_top_str ~filename:"t1"
{|fn f(x,y, z, ) {
  while p(x,z) {
    var y = f(x+1,"foo");
    y = z + 1 + $ \x (y z: foo). x (x y) z $;
    break;

    let myexpr = $ \x. f ${x} ${ g(y) } $;
    if false { continue; }
    else if true { echo("elseif"); break; }
    else if !true && !false || foo { return 42; }
    else {
      let res = f(1) + f(2) +  if true { 1 } else { 2 };
      return res;
    }
    return x;
  }
  z
}

call_some_fun(g(:atom, :atom2), "bang!");
|};;

Format.printf "parsed:@ %a@." (pp_or_error Ast.pp_top) top;;



