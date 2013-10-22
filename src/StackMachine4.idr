module StackMachine4
import Tip
import Interp

%default total

mutual
  data Inst : Nat -> Nat -> Type where
    PUSH : Int -> Inst s         (S s)
    DBUG : Nat -> Inst s         (S s)
    ADD  :        Inst (S (S s)) (S s)
    SUB  :        Inst (S (S s)) (S s)
    MUL  :        Inst (S (S s)) (S s)
    DIV  :        Inst (S (S s)) (S s)
    EQL  :        Inst (S (S s)) (S s)
    LTH  :        Inst (S (S s)) (S s)
    NAY  :        Inst (S s)     (S s)
    IF   :        Inst (S (S (S s))) (S s)

  data Prog : Nat -> Nat -> Type where
    Nil  : Prog s s
    (::) : Inst s s' -> Prog s' s'' -> Prog s s''

(+++) : Prog s s' -> Prog s' s'' -> Prog s s''
(+++) Nil p2       = p2
(+++) (i :: p1) p2 = i :: ((+++) p1 p2)
infixr 10 +++

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
  weakenInst : Inst n m -> Inst (S n) (S m)
  weakenInst (PUSH i) = PUSH i
  weakenInst ADD  = ADD
  weakenInst SUB  = SUB
  weakenInst MUL  = MUL
  weakenInst DIV  = DIV
  weakenInst EQL  = EQL
  weakenInst LTH  = LTH
  weakenInst NAY  = NAY
  weakenInst IF   = IF
  weakenInst (DBUG n) = DBUG n

  weakenProg : Prog n m -> Prog (S n) (S m)
  weakenProg Nil = Nil
  weakenProg (instr :: p) = weakenInst instr :: weakenProg p

  {-data StackEff : Nat -> Nat -> Type where
    Inc  : {n : Nat} -> (m : Nat) -> StackEff n (m + n)
    Flat : {n : Nat} -> StackEff n n
    Dec  : {n : Nat} -> (m : Nat) -> StackEff (m + n) n-}

  data Eff : Type where
    Inc  : Nat -> Eff
    Dec  : Nat -> Eff
    Flat : Eff

  getProg : Nat -> Eff -> Type
  getProg n (Inc m) = Prog n (S (m + n))
  getProg n (Dec m) = Prog (S (m + n)) n
  getProg n Flat    = Prog n n

  partial
  getEff : Tip -> Eff
  getEff TipInt  = Inc 0
  getEff TipBool = Inc 0

  partial -- Should be total when finished
  compile : Expr G t -> Vect n (Prog p (S p)) -> getProg s (getEff t)
  compile (Val i)         sf    = [PUSH i]
  compile (Boo True)      sf    = [PUSH 1]
  compile (Boo False)     sf    = [PUSH 0]
  compile (OpU Nay v)     sf    = compile v sf +++ [NAY]
  {-compile (OpB o v1 v2) sf = compileOp o where
    partial -- Should be declared total when outer function compile is total
    compileOp : BinOp a b c -> (eff: (Nat, Nat) ** Prog (fst eff) (snd eff))
    compileOp Add with (compile v1 sf) 
      | ((n, (S n)) ** s1) with (compile v2 sf)
        | ((S n, S (S n)) ** s2) = ((n, S n) ** (s1 +++ s2 +++ [ADD]))
        | ((x, y) ** z) = ((0, 1) ** ([DBUG x] +++ [DBUG y] +++ [ADD]))
    compileOp Sub = compile v1 sf +++ compile v2 (map weakenProg sf) +++ [SUB]
    compileOp Mul = compile v1 sf +++ compile v2 (map weakenProg sf) +++ [MUL]
    compileOp Div = compile v1 sf +++ compile v2 (map weakenProg sf) +++ [DIV]
    compileOp Eql = compile v1 sf +++ compile v2 (map weakenProg sf) +++ [EQL]
    compileOp Lt  = compile v1 sf +++ compile v2 (map weakenProg sf) +++ [LTH]-}
  compile (If b tb fb)       sf = compile tb sf +++ 
                                  compile fb sf +++ 
                                  compile b  sf +++ [IF]
  {-compile (App (Lam b) e)    sf = compile b ((compile e sf) :: sf)
  compile (Var stop)  (e :: sf) = e
  compile (Var (pop k)) (e :: sf) = compile (Var k) sf

 
  test4 : Expr Nil TipInt
  test4 = App (Lam (If (OpU Nay (OpB Eql (Var stop) (Val 2))) (OpB Add (Val 2) (Val 3)) (Val 2))) (Val 3)

  partial
  test5 : Prog 0 1
  test5 = compile test4 Nil-}

  test4 : Expr Nil TipBool
  test4 = (OpU Nay (Boo True))

  test5 : Expr Nil TipInt
  test5 = (OpB Add (Val 1) (Val 2))
