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
    IF   : Prog s s' -> Prog s s' -> Inst (S s) s'

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
run ((IF TB FB) :: is)    (v :: vs) = let b = case v of
                                                   0 => FB
                                                   _ => TB
                                              in run (b +++ is) vs
run []             vs                 = vs

test : Prog (S s) (S s)
test = [PUSH 3] +++ [ADD]

test2 : Prog 2 1
test2 = [ADD]

test3 : Prog s (S s)
test3 = [PUSH 5]

test6 : Prog Z (S Z)
test6 = [PUSH 0, IF ([PUSH 1]) ([PUSH 2])]

test7 : Prog Z (S Z)
test7 = [PUSH 1, NAY]

using (G: Vect n Tip)
  partial
  compile : Expr G t -> Vect n (Prog s (S s)) -> Prog s (S s)
  compile (Val i)         sf    = [PUSH i]
  compile (Boo b)         sf    = case b of
                                       True => [PUSH 1]
                                       _    => [PUSH 0]
  --compile (OpB Add v1 v2)    sf = compile v1 sf +++ compile v2 sf +++ [ADD]
  --compile (OpB Sub v1 v2)    sf = compile v1 sf +++ compile v2 sf +++ [SUB]
  --compile (OpB Mul v1 v2)    sf = compile v1 sf +++ compile v2 sf +++ [MUL]
  --compile (OpB Div v1 v2)    sf = compile v1 sf +++ compile v2 sf +++ [DIV]
  --compile (OpB Eql v1 v2)    sf = compile v1 sf +++ compile v2 sf +++ [EQL]
  --compile (OpB Lt  v1 v2)    sf = compile v1 sf +++ compile v2 sf +++ [LTH]
  compile (OpU Nay v)        sf = compile v  sf +++ [NAY] 
  compile (If b tb fb)       sf = compile b  sf +++ [IF (compile tb sf) (compile fb sf)]
  compile (App (Lam b) e)    sf = compile b ((compile e sf) :: sf)
  compile (Var stop)  (e :: sf) = e
  compile (Var (pop k)) (e :: sf) = compile (Var k) sf
 
 
  test4 : Expr Nil TipInt
  test4 = If (OpU Nay (OpB Eql (Val 3) (Val 2))) (OpB Add (Val 2) (Val 3)) (Val 2)

  --partial
  --test5 : Prog 0 1
  --test5 = compile test4


