module Tip
import Decidable.Decidable
import Decidable.Equality

%default total

data Tip = TipBool | TipInt | TipPair Tip Tip | TipFun Tip Tip

---------- Properties of Tip ----------
tipIntNotTipBool : (p: TipInt = TipBool) -> _|_
tipIntNotTipBool {p = refl} impossible -- impossible makes sure that the type checker will never accept such a claim

tipIntNotTipFun : (p: TipInt = (TipFun t t')) -> _|_
tipIntNotTipFun {p = refl} impossible

tipIntNotTipPair : (p: TipInt = (TipPair t t')) -> _|_
tipIntNotTipPair {p = refl} impossible

tipBoolNotTipPair : (p: TipBool = (TipPair t t')) -> _|_
tipBoolNotTipPair {p = refl} impossible

tipFunNotTipPair : (p: (TipFun s s') = (TipPair t t')) -> _|_
tipFunNotTipPair {p = refl} impossible

tipBoolNotTipFun : (p: TipBool = (TipFun t t')) -> _|_
tipBoolNotTipFun {p = refl} impossible


----- Properties of TipFun -----
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


----- Properties of TipPair -----
tipPairFstNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (s = t -> _|_) -> (pst: s' = s') -> ((ptp: (TipPair s s') = (TipPair t s')) -> _|_)
tipPairFstNeq p {pst = refl} {ptp = refl} = ?tipPairFstNeqcase

tipPairSndNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (pst: s = s) -> (s' = t' -> _|_) -> ((ptp: (TipPair s s') = (TipPair s t')) -> _|_)
tipPairSndNeq {pst = refl} p {ptp = refl} = ?tipPairSndNeqcase

tipPairBothNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (s = t -> _|_) -> (s' = t' -> _|_) -> ((ptp: (TipPair s s') = (TipPair t t')) -> _|_)
tipPairBothNeq p p' {ptp = refl} = ?tipPairBothNeqcase



instance DecEq Tip where
  decEq TipInt         TipInt         = Yes refl
  decEq TipInt         TipBool        = No tipIntNotTipBool
  decEq TipInt         (TipPair t t') = No tipIntNotTipPair
  decEq TipInt         (TipFun t t')  = No tipIntNotTipFun
  decEq TipBool        TipBool        = Yes refl
  decEq TipBool        TipInt         = No $ negEqSym tipIntNotTipBool -- negEqSym : (a = b -> _|_) -> (b = a -> _|_)
  decEq TipBool        (TipPair t t') = No tipBoolNotTipPair
  decEq TipBool        (TipFun t t')  = No tipBoolNotTipFun
  decEq (TipPair t t') TipInt         = No $ negEqSym tipIntNotTipPair
  decEq (TipPair t t') TipBool        = No $ negEqSym tipBoolNotTipPair
  decEq (TipPair s s') (TipPair t t') with (decEq s t)
    decEq (TipPair s s') (TipPair s t') | Yes refl with (decEq s' t')
      decEq (TipPair s s') (TipPair s s') | (Yes refl) | (Yes refl) = Yes refl
      decEq (TipPair s s') (TipPair s t') | (Yes refl) | (No p) = No ?tipDecEqTipPairYesNocase
    decEq (TipPair s s') (TipPair t t') | No p with (decEq s' t')
      decEq (TipPair s s') (TipPair t s') | (No p) | (Yes refl) = No ?tipDecEqTipPairNoYescase
      decEq (TipPair s s') (TipPair t t') | (No p) | (No p') = No $ tipPairBothNeq p p'
  decEq (TipPair t t') (TipFun t t')  = No $ negEqSym tipFunNotTipPair
  decEq (TipFun t t')  TipInt         = No $ negEqSym tipIntNotTipFun
  decEq (TipFun t t')  TipBool        = No $ negEqSym tipBoolNotTipFun
  decEq (TipFun t t')  (TipPair s s') = No tipFunNotTipPair
  decEq (TipFun s s')  (TipFun t t')  with (decEq s t)
    decEq (TipFun s s') (TipFun s t') | Yes refl with (decEq s' t')
      decEq (TipFun s s') (TipFun s s') | (Yes refl) | (Yes refl) = Yes refl
      decEq (TipFun s s') (TipFun s t') | (Yes refl) | (No p) = No ?tipDecEqTipFunYesNocase
    decEq (TipFun s s') (TipFun t t') | No p with (decEq s' t')
      decEq (TipFun s s') (TipFun t s') | (No p) | (Yes refl) = No $ ?tipDecEqTipFunNoYescase
      decEq (TipFun s s') (TipFun t t') | (No p) | (No p') = No $ tipFunBothNeq p p' --?tipDecEqTipFunNoNocase

---------- Proofs ----------

Tip.tipDecEqTipPairNoYescase = proof {
  intros;
  refine tipPairFstNeq;
  trivial;
  trivial;
  trivial;
  trivial;
}

Tip.tipDecEqTipPairYesNocase = proof {
  intros;
  refine tipPairSndNeq;
  refine refl;
  trivial;
  trivial;
  trivial;
}

Tip.tipPairSndNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipPairFstNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipPairBothNeqcase = proof {
  intros;
  refine p';
  refine refl;
}

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
