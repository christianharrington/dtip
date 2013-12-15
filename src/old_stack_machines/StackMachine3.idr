module StackMachine3
import Tip
import Interp

%default total

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

  weaken : Prog n m -> Prog (S n) (S m)
  weaken Nil = Nil
  weaken (instr :: p) = weakenInst instr :: weaken p

  partial -- Should be total when finished
  compile : Expr G t -> Vect n (Prog s (S s)) -> Prog s (S s)
  compile (Val i)         sf    = [PUSH i]
  compile (Boo True)      sf    = [PUSH 1]
  compile (Boo False)     sf    = [PUSH 0]
  compile {s} (OpB o v1 v2) sf = compileOp o where
    partial -- Should be declared total when outer function compile is total
    compileOp : BinOp a b c -> Prog s (S s)
    compileOp Add = compile v1 sf +++ compile v2 (map weaken sf) +++ [ADD]
    compileOp Sub = compile v1 sf +++ compile v2 (map weaken sf) +++ [SUB]
    compileOp Mul = compile v1 sf +++ compile v2 (map weaken sf) +++ [MUL]
    compileOp Div = compile v1 sf +++ compile v2 (map weaken sf) +++ [DIV]
    compileOp Eql = compile v1 sf +++ compile v2 (map weaken sf) +++ [EQL]
    compileOp Lt  = compile v1 sf +++ compile v2 (map weaken sf) +++ [LTH]
  compile (OpU Nay v)        sf = compile v  sf +++ [NAY] 
  compile (If b tb fb)       sf = compile tb sf +++ 
                                  compile fb (map weaken sf) +++ 
                                  compile b  (map (weaken . weaken) sf) +++ [IF]
  compile (App (Lam b) e)    sf = compile b ((compile e sf) :: sf)
  compile (Var stop)  (e :: sf) = e
  compile (Var (pop k)) (e :: sf) = compile (Var k) sf

 
  test4 : Expr Nil TipInt
  test4 = App (Lam (If (OpU Nay (OpB Eql (Var stop) (Val 2))) (OpB Add (Val 2) (Val 3)) (Val 2))) (Val 3)

  partial
  test5 : Prog 0 1
  test5 = compile test4 Nil
