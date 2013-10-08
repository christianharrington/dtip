module Tip
import Decidable.Decidable
import Decidable.Equality

%default total

data Tip = TipUnit | TipBool | TipInt | TipProd Tip Tip | TipSum Tip Tip | TipFun Tip Tip

---------- Properties of Tip ----------

-- TipUnit
tipUnitNotTipInt : (p: TipUnit = TipInt) -> _|_
tipUnitNotTipInt {p = refl} impossible -- impossible makes sure that the type checker will never accept such a claim

tipUnitNotTipBool : (p: TipUnit = TipBool) -> _|_
tipUnitNotTipBool {p = refl} impossible

tipUnitNotTipProd : (p: TipUnit = (TipProd t t')) -> _|_
tipUnitNotTipProd {p = refl} impossible

tipUnitNotTipSum : (p: TipUnit = (TipSum t t')) -> _|_
tipUnitNotTipSum {p = refl} impossible

tipUnitNotTipFun : (p: TipUnit = (TipFun t t')) -> _|_
tipUnitNotTipFun {p = refl} impossible

-- TipBool
tipBoolNotTipInt : (p: TipBool = TipInt) -> _|_
tipBoolNotTipInt {p = refl} impossible

tipBoolNotTipProd : (p: TipBool = (TipProd t t')) -> _|_
tipBoolNotTipProd {p = refl} impossible

tipBoolNotTipSum : (p: TipBool = (TipSum t t')) -> _|_
tipBoolNotTipSum {p = refl} impossible

tipBoolNotTipFun : (p: TipBool = (TipFun t t')) -> _|_
tipBoolNotTipFun {p = refl} impossible

-- TipInt
tipIntNotTipProd : (p: TipInt = (TipProd t t')) -> _|_
tipIntNotTipProd {p = refl} impossible

tipIntNotTipSum : (p: TipInt = (TipSum t t')) -> _|_
tipIntNotTipSum {p = refl} impossible

tipIntNotTipFun : (p: TipInt = (TipFun t t')) -> _|_
tipIntNotTipFun {p = refl} impossible

-- TipProd
tipProdNotTipSum : (p: (TipProd s s') = (TipSum t t')) -> _|_
tipProdNotTipSum {p = refl} impossible

tipProdNotTipFun : (p: (TipProd s s') = (TipFun t t')) -> _|_
tipProdNotTipFun {p = refl} impossible

-- TipSum
tipSumNotTipFun : (p: (TipSum s s') = (TipFun t t')) -> _|_
tipSumNotTipFun {p = refl} impossible

-- TipFun


----- Properties of TipProd -----
tipProdFstNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (s = t -> _|_) -> (pst: s' = s') -> ((ptp: (TipProd s s') = (TipProd t s')) -> _|_)
tipProdFstNeq p {pst = refl} {ptp = refl} = ?tipProdFstNeqcase

tipProdSndNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (pst: s = s) -> (s' = t' -> _|_) -> ((ptp: (TipProd s s') = (TipProd s t')) -> _|_)
tipProdSndNeq {pst = refl} p {ptp = refl} = ?tipProdSndNeqcase

tipProdBothNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (s = t -> _|_) -> (s' = t' -> _|_) -> ((ptp: (TipProd s s') = (TipProd t t')) -> _|_)
tipProdBothNeq p p' {ptp = refl} = ?tipProdBothNeqcase


----- Properties of TipSum -----
tipSumLeftNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (s = t -> _|_) -> (pst: s' = s') -> ((pts: (TipSum s s') = (TipSum t s')) -> _|_)
tipSumLeftNeq p {pst = refl} {pts = refl} = ?tipSumLeftNeqcase

tipSumRightNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (pst: s = s) -> (s' = t' -> _|_) -> ((pts: (TipSum s s') = (TipSum s t')) -> _|_)
tipSumRightNeq {pst = refl} p {pts = refl} = ?tipSumRightNeqcase

tipSumBothNeq : {s: Tip, s': Tip, t: Tip, t': Tip} -> (s = t -> _|_) -> (s' = t' -> _|_) -> ((pts: (TipSum s s') = (TipSum t t')) -> _|_)
tipSumBothNeq p p' {pts = refl} = ?tipSumBothNeqcase

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


instance DecEq Tip where
  decEq TipUnit        TipUnit        = Yes refl
  decEq TipUnit        TipBool        = No tipUnitNotTipBool
  decEq TipUnit        TipInt         = No tipUnitNotTipInt
  decEq TipUnit        (TipProd t t') = No tipUnitNotTipProd
  decEq TipUnit        (TipSum t t')  = No tipUnitNotTipSum
  decEq TipUnit        (TipFun t t')  = No tipUnitNotTipFun
  
  decEq TipBool        TipBool        = Yes refl
  decEq TipBool        TipUnit        = No $ negEqSym tipUnitNotTipBool -- negEqSym : (a = b -> _|_) -> (b = a -> _|_)
  decEq TipBool        TipInt         = No tipBoolNotTipInt
  decEq TipBool        (TipProd t t') = No tipBoolNotTipProd
  decEq TipBool        (TipSum t t')  = No tipBoolNotTipSum
  decEq TipBool        (TipFun t t')  = No tipBoolNotTipFun
  
  decEq TipInt         TipInt         = Yes refl
  decEq TipInt         TipUnit        = No $ negEqSym tipUnitNotTipInt
  decEq TipInt         TipBool        = No $ negEqSym tipBoolNotTipInt
  decEq TipInt         (TipProd t t') = No tipIntNotTipProd
  decEq TipInt         (TipSum t t')  = No tipIntNotTipSum
  decEq TipInt         (TipFun t t')  = No tipIntNotTipFun
  
  decEq (TipProd s s') (TipProd t t') with (decEq s t)
    decEq (TipProd s s') (TipProd s t') | Yes refl with (decEq s' t')
      decEq (TipProd s s') (TipProd s s') | (Yes refl) | (Yes refl) = Yes refl
      decEq (TipProd s s') (TipProd s t') | (Yes refl) | (No p) = No ?tipDecEqTipProdYesNocase
    decEq (TipProd s s') (TipProd t t') | No p with (decEq s' t')
      decEq (TipProd s s') (TipProd t s') | (No p) | (Yes refl) = No ?tipDecEqTipProdNoYescase
      decEq (TipProd s s') (TipProd t t') | (No p) | (No p') = No $ tipProdBothNeq p p'
  decEq (TipProd t t') TipUnit        = No $ negEqSym tipUnitNotTipProd
  decEq (TipProd t t') TipBool        = No $ negEqSym tipBoolNotTipProd
  decEq (TipProd t t') TipInt         = No $ negEqSym tipIntNotTipProd
  decEq (TipProd s s') (TipSum t t')  = No tipProdNotTipSum
  decEq (TipProd s s') (TipFun t t')  = No tipProdNotTipFun

  decEq (TipSum s s')  (TipSum t t')  with (decEq s t)
    decEq (TipSum s s') (TipSum s t') | Yes refl with (decEq s' t')
      decEq (TipSum s s') (TipSum s s') | (Yes refl) | (Yes refl) = Yes refl
      decEq (TipSum s s') (TipSum s t') | (Yes refl) | (No p) = No ?tipDecEqTipSumYesNocase
    decEq (TipSum s s') (TipSum t t') | No p with (decEq s' t')
      decEq (TipSum s s') (TipSum t s') | (No p) | (Yes refl) = No ?tipDecEqTipSumNoYescase
      decEq (TipSum s s') (TipSum t t') | (No p) | (No p') = No $ tipSumBothNeq p p' 
  decEq (TipSum s s')  (TipFun t t')  = No tipSumNotTipFun
  decEq (TipSum t t')  TipUnit        = No $ negEqSym tipUnitNotTipSum
  decEq (TipSum t t')  TipBool        = No $ negEqSym tipBoolNotTipSum
  decEq (TipSum t t')  TipInt         = No $ negEqSym tipIntNotTipSum
  decEq (TipSum s s')  (TipProd t t') = No $ negEqSym tipProdNotTipSum

  decEq (TipFun s s')  (TipFun t t')  with (decEq s t)
    decEq (TipFun s s') (TipFun s t') | Yes refl with (decEq s' t')
      decEq (TipFun s s') (TipFun s s') | (Yes refl) | (Yes refl) = Yes refl
      decEq (TipFun s s') (TipFun s t') | (Yes refl) | (No p) = No ?tipDecEqTipFunYesNocase
    decEq (TipFun s s') (TipFun t t') | No p with (decEq s' t')
      decEq (TipFun s s') (TipFun t s') | (No p) | (Yes refl) = No $ ?tipDecEqTipFunNoYescase
      decEq (TipFun s s') (TipFun t t') | (No p) | (No p') = No $ tipFunBothNeq p p' --?tipDecEqTipFunNoNocase
  decEq (TipFun t t')  TipUnit        = No $ negEqSym tipUnitNotTipFun
  decEq (TipFun t t')  TipInt         = No $ negEqSym tipIntNotTipFun
  decEq (TipFun t t')  TipBool        = No $ negEqSym tipBoolNotTipFun
  decEq (TipFun s s')  (TipProd s s') = No $ negEqSym tipProdNotTipFun
  decEq (TipFun s s')  (TipSum s s')  = No $ negEqSym tipSumNotTipFun

---------- Proofs ----------

Tip.tipDecEqTipSumYesNocase = proof {
  intros;
  refine tipSumRightNeq;
  refine refl;
  trivial;
  trivial;
  trivial;
}

Tip.tipDecEqTipSumNoYescase = proof {
  intros;
  refine tipSumLeftNeq;
  trivial;
  refine refl;
  trivial;
  trivial;
}

Tip.tipSumBothNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipSumRightNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipSumLeftNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipDecEqTipProdNoYescase = proof {
  intros;
  refine tipProdFstNeq;
  trivial;
  trivial;
  trivial;
  trivial;
}

Tip.tipDecEqTipProdYesNocase = proof {
  intros;
  refine tipProdSndNeq;
  refine refl;
  trivial;
  trivial;
  trivial;
}

Tip.tipProdSndNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipProdFstNeqcase = proof {
  intros;
  refine p;
  refine refl;
}

Tip.tipProdBothNeqcase = proof {
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
