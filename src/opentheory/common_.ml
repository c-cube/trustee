module H = Tiny_httpd
module Html = Tiny_httpd_html
module Error = Trustee_core.Error
module K = Trustee_core.Kernel
module Chash = Trustee_core.Chash

let spf = Printf.sprintf

let ( let@ ) f x = f x

let cls = Html.A.class_
