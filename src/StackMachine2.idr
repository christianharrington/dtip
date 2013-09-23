module StackMachine2
import Interp

%default total

mutual
  data Ctxt : Nat -> Type where
    NilG : Ctxt Z
    MkG  : (g: Ctxt n) -> Prog n g s s' -> Ctxt (S n)

  data Inst : (n: Nat) -> Ctxt n -> Nat -> Nat -> Type where
    PUSH  : Int -> Inst n g s         (S s)
    ADD   :        Inst n g (S (S s)) (S s)
    SUB   :        Inst n g (S (S s)) (S s)
    FUNC  : {g: Ctxt n} -> (i: Fin n) -> let eff = getProgEff i g in Inst n g (fst eff) (snd eff)

  data Prog : (n: Nat) -> Ctxt n -> Nat -> Nat -> Type where
    Nil  : Prog n g s s
    (::) : Inst n g s s' -> Prog n g s' s'' -> Prog n g s s''

  getProgEff : Fin n -> Ctxt n -> (Nat, Nat)
  getProgEff fZ     (MkG {s=s} {s'=s'} _ _) = (s, s')
  getProgEff (fS i) (MkG ps p)              = getProgEff i ps

add5 : Prog Z NilG (S Z) (S Z)
add5 = [PUSH 5, ADD]
test : Prog (S Z) (MkG NilG add5) Z (S Z)
test = [PUSH 2, FUNC 0]

partial
run : (g : Ctxt n) -> Prog n g s s' -> Vect s Int -> Vect s' Int
run g (PUSH v :: is) vs               = run g is (v :: vs)
run g (ADD    :: is) (v1 :: v2 :: vs) = run g is ((v1 + v2) :: vs)
run g (SUB    :: is) (v1 :: v2 :: vs) = run g is ((v1 - v2) :: vs)
run g []             vs               = vs
