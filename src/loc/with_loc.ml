open Common_

type 'a t = {
  loc: Loc.t;
  view: 'a;
}

let[@inline] loc self = self.loc
let[@inline] view self = self.view
