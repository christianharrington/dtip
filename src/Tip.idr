module Tip
import Decidable.Decidable
import Decidable.Equality

%default total

data Tip = TipBool | TipInt | TipFun Tip Tip

---------- Properties of Tip ----------
tipIntNotTipBool : (p: TipInt = TipBool) -> _|_
tipIntNotTipBool {p = refl} impossible -- impossible makes sure that the type checker will never accept such a claim

tipIntNotTipFun : (p: TipInt = (TipFun t t')) -> _|_
tipIntNotTipFun {p = refl} impossible

tipBoolNotTipFun : (p: TipBool = (TipFun t t')) -> _|_
tipBoolNotTipFun {p = refl} impossible

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

---------- Proofs ----------

Tip.tipDecEqTipFunNoYescase = proof {
  intros;
  refine tipFunArgsNeq;
  trivial;
  refine refl;
  trivial;
  trivial;
}

Tip.tipDecEqTipFunYesNocase = proof {
  intros;
  refine tipFunResultNeq;
  refine refl;
  trivial;
  trivial;
  trivial;
}

Tip.tipFunBothNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipFunArgsNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipFunResultNeqcase = proof {
  intros;
  refine p;
  refine refl;
}
