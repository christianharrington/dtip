module StackMachine6
import Tip
import Interp
import Bounded

%default total

data StackInst : Nat -> Nat -> Nat -> Type where
  PUSH : Int -> StackInst s (S s) labels

data ArithInst : Nat -> Nat -> Nat -> Type where
  ADD : ArithInst (S (S s)) s labels

data Inst : Nat -> Nat -> Nat -> Type where
  Stk  : StackInst s s' labels -> Inst s s' labels
  Arth : ArithInst s s' labels -> Inst s s' labels
{-
data Inst : Nat -> Nat -> Nat -> Type where
  PUSH : Int -> Inst s (S s) labels
  ADD  : Inst (S (S s)) (S s) labels -}

data Prog : Nat -> Nat -> Nat -> Type where
  Nil  : Prog s s  labels
  (::) : Inst s s' labels -> Prog s' s'' labels -> Prog s s'' labels

(+++) : Prog s s' labels -> Prog s' s'' labels -> Prog s s'' labels
(+++) Nil p2       = p2
(+++) (i :: p1) p2 = i :: ((+++) p1 p2)
infixr 10 +++

data Program = MkProg (Prog Z e Z)

test : Program
test = MkProg [Stk (PUSH 1), Stk (PUSH 2), Arth ADD]

test2 : Prog s (S s) s
test2 = [Stk (PUSH 1)]

using (G: Vect n Tip)
  partial
  compile : Expr G t -> Prog s s' labels
  compile {s=Z} {s'=S Z} (Val i) = [Stk (PUSH i)]
  compile (OpB Add v1 v2) = compile v1 +++ compile v2 +++ [Arth ADD] 
  