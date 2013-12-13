module StackMachine4
import Tip
import Interp
import NatCmp

%default total

data Eff : Type where
  Flat :        Eff 
  Inc  : Nat -> Eff
  Dec  : Nat -> Eff

stackProduce : Eff -> Nat -> Nat
stackProduce Flat n = n
stackProduce (Inc Z) n = S n
stackProduce (Inc m) n = S (m+n)
stackProduce (Dec _) n = n

stackReq : Eff -> Nat -> Nat
stackReq Flat n = n
stackReq (Dec Z) n = S n
stackReq (Dec m) n = S (m+n)
stackReq (Inc x) n = n

%assert_total
effPlus : Eff -> Eff -> Eff
effPlus Flat b = b
effPlus a Flat = a
effPlus (Inc x) (Inc y) = Inc (S (x + y))
effPlus (Inc Z) (Dec (S x)) = Dec x
effPlus (Inc Z) (Dec Z) = Flat
effPlus (Inc (S x)) (Dec (S y)) = effPlus (Inc x) (Dec y)
effPlus (Inc (S x)) (Dec Z) = Inc x
effPlus (Dec x) (Dec y) = Dec (S (x + y))
effPlus (Dec Z) (Inc (S x)) = Inc x
effPlus (Dec Z) (Inc Z) = Flat
effPlus (Dec (S x)) (Inc (S y)) = effPlus (Dec x) (Inc y)
effPlus (Dec (S x)) (Inc Z) = Dec x

using(E: Vect n Eff)
  data HasEffect : Vect n Eff -> Eff -> Type where
    stop : HasEffect (e :: E) e
    pop  : HasEffect E e -> HasEffect (f :: E) e

  mutual
    data Inst : Nat -> Nat -> Type where
      PUSH : Int -> Inst s         (S s)
      ADD  :        Inst (S (S s)) (S s)
      SUB  :        Inst (S (S s)) (S s)
      MUL  :        Inst (S (S s)) (S s)
      DIV  :        Inst (S (S s)) (S s)
      EQL  :        Inst (S (S s)) (S s)
      LTH  :        Inst (S (S s)) (S s)
      NAY  :        Inst (S s)     (S s)
      IF   :        Inst (S (S (S s))) (S s)
      FST  : {e : Eff} -> Nat -> Inst (stackReq e s) (stackProduce e s)
      SND  : (e : Eff) -> Nat -> Inst (stackReq e s) (stackProduce e s)
      CALL : (e : Eff) -> HasEffect E e -> Inst (stackReq e s) (stackProduce e s)

    partial
    constructInst : Eff -> Nat -> Type
    constructInst Flat n = Inst n n

    data Prog : Nat -> Nat -> Type where
      Nil  : Prog s s
      (::) : Inst s s' -> Prog s' s'' -> Prog s s''

infixr 10 +++
(+++) : Prog s s' -> Prog s' s'' -> Prog s s''
(+++) Nil p2       = p2
(+++) (i :: p1) p2 = i :: (p1 +++ p2)

partial -- We think it's total
{-
  Consider:
    If we want to prove that the well-typed interpreter and the run function both evaluate the same program to the same value,
    we have to find out how these two can be equated
-}
run : Prog s s' -> Vect s Int -> Vect s' Int
run (PUSH v :: is) vs               = run is (v :: vs)
run (ADD    :: is) (v1 :: v2 :: vs) = run is ((v1 + v2) :: vs)
run (SUB    :: is) (v1 :: v2 :: vs) = run is ((v2 - v1) :: vs)
run (MUL    :: is) (v1 :: v2 :: vs) = run is ((v1 * v2) :: vs)
run (DIV    :: is) (v1 :: v2 :: vs) = run is ((cast ((cast v2) / (cast v1))) :: vs)
run (EQL    :: is) (v1 :: v2 :: vs) = let b = case (v1 == v2) of
                                                   True  => 1
                                                   False => 0
                                              in run is (b :: vs)
run (LTH    :: is) (v1 :: v2 :: vs) = let b = case (v1 < v2) of
                                                   True  => 1
                                                   False => 0
                                              in run is (b :: vs)
run (NAY    :: is)        (v :: vs) = let b = case v of
                                                   0 => 1
                                                   _ => 0
                                              in run is (b :: vs)
run (IF     :: is)        (b :: e1 :: e2 :: vs) = let v = case b of
                                                   0 => e1
                                                   _ => e2
                                              in run is (v :: vs)
run []             vs                 = vs

using (G: Vect n Tip)

  {-data StackEff : Nat -> Nat -> Type where
    Inc  : {n : Nat} -> (m : Nat) -> StackEff n (m + n)
    Flat : {n : Nat} -> StackEff n n
    Dec  : {n : Nat} -> (m : Nat) -> StackEff (m + n) n-}


  getProg : Nat -> Eff -> Type
  getProg n (Inc m) = Prog n (S (m + n))
  getProg n (Dec m) = Prog (S (m + n)) n
  getProg n Flat    = Prog n n

  getEff : Tip -> Eff
  getEff TipUnit        = Flat
  getEff TipInt         = Inc 0
  getEff TipBool        = Inc 0
  getEff (TipProd T T') = Flat
  getEff (TipSum T T')  = Inc 1
  getEff (TipFun T T')  = getEff T'

  getTip : Expr G t -> Tip
  getTip {t=t} e = t
 
  data StackFrame : Vect n Tip -> Nat -> Type where
    Nill : StackFrame [] Z
    (:::) : Expr G t -> StackFrame G n -> StackFrame (t :: G) (S n)
  infixr 10 :::
  
  partial -- Should be total when finished
  compile : Expr G t -> StackFrame G n -> getProg s (getEff t)
  compile U                 sf    = StackMachine4.Nil
  compile (Val i)           sf    = [PUSH i]
  compile (Boo True)        sf    = [PUSH 1]
  compile (Boo False)       sf    = [PUSH 0]
  compile (OpU Nay v)       sf    = compile v sf +++ [NAY]
  compile (OpB o v1 v2) sf = compileOp o v1 v2 sf where
    partial -- Should be declared total when outer function compile is total
    compileOp : BinOp a b c -> Expr G a -> Expr G b -> StackFrame G n -> getProg s (getEff c)
    compileOp Add e1 e2 sf = compile e1 sf +++ compile e2 sf +++ [ADD]
    compileOp Sub e1 e2 sf = compile e1 sf +++ compile e2 sf +++ [SUB]
    compileOp Mul e1 e2 sf = compile e1 sf +++ compile e2 sf +++ [MUL]
    compileOp Div e1 e2 sf = compile e1 sf +++ compile e2 sf +++ [DIV]
    compileOp Eql e1 e2 sf = compile e1 sf +++ compile e2 sf +++ [EQL]
    compileOp Lt  e1 e2 sf = compile e1 sf +++ compile e2 sf +++ [LTH]
  compile (If b tb fb) {t=TipUnit} sf = []
  compile (If b tb fb) {t=TipBool} sf = compile tb sf +++ compile fb sf +++ compile b  sf +++ [IF]
  compile (If b tb fb) {t=TipInt} sf = compile tb sf +++ compile fb sf +++ compile b  sf +++ [IF]
  compile (App (Lam b) e) sf = compile b (e ::: sf)
  compile (Var stop) {G = x :: xs} (e ::: sf) = compile e sf
  compile (Var (pop k)) (e ::: sf) = compile (Var k) sf
  compile (Fst e) {t=TipInt} sf = (FST Z {e=(getEff TipInt)}) :: (compile e sf)
  --compile (Fst (Var stop)) ((Pair e _) ::: sf) = compile e sf
  --compile (Fst (Var (pop k)) (e ::: sf)) compile (Fst k) sf
  

  
  test4 : Expr Nil TipInt
  test4 = App (Lam (If (OpU Nay (OpB Eql (Var stop) (Val 2))) (OpB Add (Val 2) (Val 3)) (Val 2))) (Val 3)

  partial
  test5 : Prog 0 1
  test5 = compile test4 Nill

{-  test4 : Expr Nil TipBool
  test4 = (OpU Nay (Boo True))

  test5 : Expr Nil TipInt
  test5 = (OpB Add (Val 1) (Val 2))-}
