module StackMachine3
import Interp

%default total

data Inst : Nat -> Nat -> Type where
  PUSH  : Int -> Inst s         (S s)
  ADD   :        Inst (S (S s)) (S s)
  SUB   :        Inst (S (S s)) (S s)
  MUL   :        Inst (S (S s)) (S s)
  DIV   :        Inst (S (S s)) (S s)

data Prog : Nat -> Nat -> Type where
  Nil  : Prog s s
  (::) : Inst s s' -> Prog s' s'' -> Prog s s''

(+++) : Prog s s' -> Prog s' s'' -> Prog s s''
(+++) Nil p2       = p2
(+++) (i :: p1) p2 = i :: ((+++) p1 p2)
infixr 10 +++

partial
run : Prog s s' -> Vect s Int -> Vect s' Int
run (PUSH v :: is) vs               = run is (v :: vs)
run (ADD    :: is) (v1 :: v2 :: vs) = run is ((v1 + v2) :: vs)
run (SUB    :: is) (v1 :: v2 :: vs) = run is ((v2 - v1) :: vs)
run (MUL    :: is) (v1 :: v2 :: vs) = run is ((v1 * v2) :: vs)
run (DIV    :: is) (v1 :: v2 :: vs) = run is ((cast ((cast v2) / (cast v1))) :: vs)
run []             vs               = vs

test : Prog Z (S Z)
test = [PUSH 100, PUSH 3, DIV]

test2 : Prog 2 1
test2 = [ADD]

test3 : Prog 0 1
test3 = [PUSH 5]

using (G: Vect n Tip)
  partial
  compile : Expr G t -> Prog Z (S Z)
  compile (Val i)         = [PUSH i]
--  compile (Ope (+) v1 v2) = let p = compile v1 +++ compile v2 +++ [ADD] in p
