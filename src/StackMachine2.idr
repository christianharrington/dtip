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
    GOTO  : {g: Ctxt n} -> (i: Fin n) -> let eff = getProgEff i g in Inst n g (fst eff) (snd eff)

  data Prog : (n: Nat) -> Ctxt n -> Nat -> Nat -> Type where
    Nil  : Prog n g s s
    (::) : Inst n g s s' -> Prog n g s' s'' -> Prog n g s s''

  getProgEff : Fin n -> Ctxt n -> (Nat, Nat)
  getProgEff fZ     (MkG {s=s} {s'=s'} _ _) = (s, s')
  getProgEff (fS i) (MkG ps p)              = getProgEff i ps

(+++) : Prog n g s s' -> Prog n g s' s'' -> Prog n g s s''
(+++) Nil p2       = p2
(+++) (i :: p1) p2 = i :: ((+++) p1 p2)
infixr 10 +++

{-changeInstCtxt : Inst n g s s' -> (g': Ctxt n') -> Inst n' g' s s'
changeInstCtxt (PUSH i) g' {n'} = PUSH i {g=g'} {n=n'}
changeInstCtxt (ADD) g' {n'}    = ADD    {g=g'} {n=n'}
changeInstCtxt (SUB) g' {n'}    = SUB    {g=g'} {n=n'}
changeInstCtxt (GOTO i) g' {n'} = GOTO i {g=g'} {n=n'}

partial
mergeCtxt : Prog n g s s' -> Ctxt n' -> Prog n' g' s s'
mergeCtxt [] g'       = StackMachine2.Nil
mergeCtxt {n'} (x :: xs) g' = (::) {n=n'} {g=g'} (changeInstCtxt x g') (mergeCtxt xs g')-}

add5 : Prog Z NilG (S Z) (S Z)
add5 = [PUSH 5, ADD]
test : Prog (S Z) (MkG NilG add5) Z (S Z)
test = [PUSH 2, GOTO 0]

run : (g : Ctxt n) -> Prog n g s s' -> Vect s Int -> Vect s' Int
run g (PUSH v :: is) vs               = run g is (v :: vs)
run g (ADD    :: is) (v1 :: v2 :: vs) = run g is ((v1 + v2) :: vs)
run g (SUB    :: is) (v1 :: v2 :: vs) = run g is ((v1 - v2) :: vs)
run (MkG g' f) (GOTO i {g=(MkG g' f)} :: is) vs with (run g' f vs)
  | vs     = run (MkG g' f) is vs
run g []             vs               = vs
