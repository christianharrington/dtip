module Interp
import Decidable.Decidable
import Decidable.Equality

%default total

data Tip = TipBool | TipInt | TipFun Tip Tip

---------- Properties of Tip ----------
-- tipFunEq : (ps: Dec (s = t)) -> (pt: Dec (s' = t')) -> Dec (TipFun s s' = TipFun t t')
-- tipFunEq (Yes ps) (Yes pt) = Yes ?tipFunEqcase1
-- tipFunEq (Yes ps) (No pt)  = No ?tipFunEqcase2
-- tipFunEq (No ps)  (Yes pt) = No ?tipFunEqcase3
-- tipFunEq (No ps)  (No pt)  = No ?tipFunEqcase4

tipIntNotTipBool : (p: TipInt = TipBool) -> _|_
tipIntNotTipBool {p = refl} impossible -- impossible makes sure that the type checker will never accept such a claim

tipIntNotTipFun : (p: TipInt = (TipFun t t')) -> _|_
tipIntNotTipFun {p = refl} impossible

tipBoolNotTipFun : (p: TipBool = (TipFun t t')) -> _|_
tipBoolNotTipFun {p = refl} impossible

-- tipFunEqImpliesArgEq : (TipFun s s' = TipFun t t') -> (s = t)
-- tipFunEqImpliesArgEq p = ?tipFunEqImpliesArgEqYescase
-- --tipFunEqImpliesArgEq (No p)  = ?tipFunEqImpliesArgEqNocase

-- tipFunEqImpliesResultEq : (ptf: Dec (TipFun s s' = TipFun t t')) -> Dec (s' = t')
-- tipFunEqImpliesResultEq (Yes p) = ?tipFunEqImpliesResultEqYescase
-- tipFunEqImpliesResultEq (No p)  = ?tipFunEqImpliesResultEqNocase

{-
     ¬ (s = t)      (s' = s')
  -----------------------------
  ¬ (TipFun s s' = TipFun t s')
-}
tipFunArgsNeq : {s: Tip, s': Tip, t: Tip, t':Tip} -> (pst: s = t -> _|_) -> (ps': s' = s') -> ((ptf: (TipFun s s') = (TipFun t s')) -> _|_)
tipFunArgsNeq p {ps' = refl} {pst = refl} = ?tipFunArgsNeqcase 

{-
     (s = s)     ¬ (s' = t')
  -----------------------------
  ¬ (TipFun s s' = TipFun s t')
-}
tipFunResultNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (ps: s = s) -> (s' = t' -> _|_) -> ((ptf: (TipFun s s') = (TipFun s t')) -> _|_)
tipFunResultNeq {ps = refl} p {ptf = refl} = ?tipFunResultNeqcase

{-
    ¬ (s = t)     ¬ (s' = t')
  -----------------------------
  ¬ (TipFun s s' = TipFun t t')
-}
tipFunBothNeq : {s: Tip, s': Tip, t: Tip, t':Tip} -> (s = t -> _|_) -> (s' = t' -> _|_) -> ((ptf: (TipFun s s') = (TipFun t t')) -> _|_)
tipFunBothNeq p p' {ptf = refl} = ?tipFunBothNeqcase 

instance DecEq Tip where
  decEq TipInt        TipInt        = Yes refl
  decEq TipBool       TipBool       = Yes refl
  decEq TipInt        TipBool       = No tipIntNotTipBool
  decEq TipBool       TipInt        = No $ negEqSym tipIntNotTipBool -- negEqSym : (a = b -> _|_) -> (b = a -> _|_)
  decEq TipInt        (TipFun t t') = No tipIntNotTipFun
  decEq (TipFun t t') TipInt        = No $ negEqSym tipIntNotTipFun
  decEq TipBool       (TipFun t t') = No tipBoolNotTipFun
  decEq (TipFun t t') TipBool       = No $ negEqSym tipBoolNotTipFun
  decEq (TipFun s s') (TipFun t t') with (decEq s t)
    decEq (TipFun s s') (TipFun s t') | Yes refl with (decEq s' t')
      decEq (TipFun s s') (TipFun s s') | (Yes refl) | (Yes refl) = Yes refl
      decEq (TipFun s s') (TipFun s t') | (Yes refl) | (No p) = No ?tipDecEqTipFunYesNocase
    decEq (TipFun s s') (TipFun t t') | No p with (decEq s' t')
      decEq (TipFun s s') (TipFun t s') | (No p) | (Yes refl) = No $ ?tipDecEqTipFunNoYescase
      decEq (TipFun s s') (TipFun t t') | (No p) | (No p') = No $ tipFunBothNeq p p' --?tipDecEqTipFunNoNocase


    -- tipFunEq (decEq s t) (decEq s' t')

-- instance Eq Tip where
--   TipInt     == TipInt         = True
--   TipBool    == TipBool        = True
--   (TipFun f x) == (TipFun g y) = (f == g) && (x == y)
--   _ == _                       = False

interpTip : Tip -> Type
interpTip TipInt  = Int
interpTip TipBool = Bool
interpTip (TipFun T T') = interpTip T -> interpTip T'

using (G: Vect n Tip)
  data HasType : (i : Fin n) -> Vect n Tip -> Tip -> Type where
    stop : HasType fZ (t :: G) t
    pop  : HasType k G t -> HasType (fS k) (u :: G) t 

  data Expr : Vect n Tip -> Tip -> Type where
    Var : HasType i G t -> Expr G t
    Val : (i : Int) -> Expr G TipInt
    Lam : Expr (t :: G) t' -> Expr G (TipFun t t')
    App : Expr G (TipFun t t') -> Expr G t -> Expr G t'
    Ope : (interpTip a -> interpTip b -> interpTip c) -> Expr G a -> Expr G b -> Expr G c

  data Env : Vect n Tip -> Type where
    Nil  : Env Nil
    (::) : interpTip a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTip t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  interp : Env G -> Expr G t -> interpTip t
  interp env (Var k)     = lookup k env
  interp env (Val i)     = i
  interp env (Lam e)     = \x => interp (x :: env) e
  interp env (App f a)   = interp env f (interp env a)
  interp env (Ope f a b) = f (interp env a) (interp env b)

  dsl expr
    lambda      = Lam
    variable    = Var
    index_first = stop
    index_next  = pop

  ----- Examples -----
  val : Expr Nil TipInt
  val = Val 0

  lam : Expr Nil (TipFun TipInt TipInt)
  lam = expr (\x => x)

  add' : Expr Nil (TipFun TipInt (TipFun TipInt TipInt))
  add' = expr (\x => (\y => Ope (+) x y))

---------- Proofs ----------

Interp.tipDecEqTipFunNoYescase = proof {
  intros;
  refine tipFunArgsNeq;
  trivial;
  refine refl;
  trivial;
  trivial;
}

Interp.tipDecEqTipFunYesNocase = proof {
  intros;
  refine tipFunResultNeq;
  refine refl;
  trivial;
  trivial;
  trivial;
}

Interp.tipFunBothNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Interp.tipFunArgsNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Interp.tipFunResultNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

-- Interp.tipFunEqcase1 = proof {
--   intros;
--   rewrite ps;
--   rewrite pt;
--   refine refl;
-- }

