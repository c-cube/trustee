open Sigs

include Types

module Expr = Expr
module Const = Const
module Const_def = Const.Const_def
module Sequent = Sequent
module Subst = Subst
module Proof = Trustee_core__Proof
module Linear_proof = Proof.Linear_proof
module Thm = Thm
module Ctx = Ctx
module Theory = Theory

module Var = struct
  include Types.Var
end
