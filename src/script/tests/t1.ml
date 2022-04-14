
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

fn g(x) { x }
|};;

Format.printf "parsed:@ %a@." (pp_or_error Ast.pp_top) top;;


