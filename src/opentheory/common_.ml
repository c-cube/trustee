module Trace = Trace_core
module H = Tiny_httpd
module Html = Tiny_httpd_html
module Error = Trustee_core.Error
module K = Trustee_core.Kernel
module Chash = Trustee_core.Chash

let spf = Printf.sprintf
let ( let@ ) = ( @@ )
let cls = Html.A.class_
