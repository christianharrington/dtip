module StackMachine5
import Tip
import Interp

%default total

data Eff : Type where
  Inc  : Nat -> Eff
  Dec  : Nat -> Eff
  Flat : Eff

data Inst : Type where
  PUSH   : Int -> Inst
  ADD    : Inst
  GOTO   : Nat -> Inst
  IFZERO : Nat -> Inst

(+++) : Vect o (Inst, Eff) -> Vect o' (Inst, Eff) -> Vect (o + o') (Inst, Eff)
(+++) []                v2 = v2
(+++) ((x, effx) :: v1) v2 with ((+++) v1 v2)
  | ((y, effy) :: vs) = (x, effx) :: (y, (chainEffects effx effy)) :: vs
infixr 10 +++

chainEffects : Eff -> Eff -> Eff
chainEffects (Inc x) (Dec y) = if x > y then Inc (x - y) else Dec (y - x) -- Not Correct
chainEffects (Dec x) (Inc y) = if x > y then Dec (x - y) else Inc (y - x) -- Not Correct
chainEffects (Dec x) (Dec y) = Dec (x + y)
chainEffects (Inc x) (Inc y) = Inc (x + y)
chainEffects  Flat    a      = a
chainEffects  a       Flat   = a

partial
getBinOpInst : BinOp a b c -> Inst
getBinOpInst Add = ADD

using (G: Vect n Tip)
  partial
  compile : Expr G t -> Vect o Eff -> (o' : Nat ** Vect o' (Inst, Eff))
  compile (Val i) _          = (1 ** [(PUSH i, Inc 0)])
  compile (OpB op v1 v2) effs with (compile v1 effs)
    | (n ** vs1) with (compile v2 effs)
      | (m ** vs2) = ((n + (m + 1)) ** vs1 +++ vs2 +++ [(getBinOpInst op, Dec 1)])
  compile {o} (If b tb fb) effs with (compile b effs)
    | (n ** bs) with (compile tb effs)
      | (m ** tbs) with (compile fb effs)
        | (p ** fbs) = ((n + (1 + (m + (1 + p)))) ** bs +++ [(IFZERO (S m), Dec 0)] +++ tbs +++ [(GOTO (n + 1 + m + o), Flat)] +++ fbs)
  