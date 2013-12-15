module StackMachine
import Tip
import Interp
import NatCmp

%default total

data Eff : Type where
  Flat:        Eff 
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

partial
getEff : Tip -> Eff
getEff TipUnit        = Flat
getEff TipInt         = Inc 0
getEff TipBool        = Inc 0
getEff (TipFun T T')  = getEff T'

using(E: Vect n Eff)
  data HasEffect : Vect n Eff -> Eff -> Type where
    stop : HasEffect (e :: E) e
    pop  : HasEffect E e -> HasEffect (f :: E) e

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
    CALL : (e : Eff) -> HasEffect E e -> Inst (stackReq e s) (stackProduce e s) 

data Prog : Nat -> Nat -> Type where
  Nil  : Prog s s
  (::) : Inst s s' -> Prog s' s'' -> Prog s s''

infixr 10 +++
(+++) : Prog s s' -> Prog s' s'' -> Prog s s''
(+++) Nil p2       = p2
(+++) (i :: p1) p2 = i :: (p1 +++ p2)

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
  
  getProg : Nat -> Eff -> Type
  getProg n (Inc m) = Prog n (S (m + n))
  getProg n (Dec m) = Prog (S (m + n)) n
  getProg n Flat    = Prog n n

  data CompEnv : Vect n Tip -> Nat -> Type where
    Nill : CompEnv [] Z
    (:::) : Expr G t -> CompEnv G n -> CompEnv (t :: G) (S n)
  infixr 10 :::
  
  partial -- Should be total when covering all terms
  compile : Expr G t -> CompEnv G n -> getProg s (getEff t)
  compile U                 ce    = StackMachine4.Nil
  compile (Val i)           ce    = [PUSH i]
  compile (Boo True)        ce    = [PUSH 1]
  compile (Boo False)       ce    = [PUSH 0]
  compile (OpU Nay v)       ce    = compile v ce +++ [NAY]
  compile (OpB o v1 v2) ce = compileOp o v1 v2 ce where
    partial -- Should be declared total when outer function compile is total
    compileOp : BinOp a b c -> Expr G a -> Expr G b -> CompEnv G n -> getProg s (getEff c)
    compileOp Add e1 e2 ce = compile e1 ce +++ compile e2 ce +++ [ADD]
    compileOp Sub e1 e2 ce = compile e1 ce +++ compile e2 ce +++ [SUB]
    compileOp Mul e1 e2 ce = compile e1 ce +++ compile e2 ce +++ [MUL]
    compileOp Div e1 e2 ce = compile e1 ce +++ compile e2 ce +++ [DIV]
    compileOp Eql e1 e2 ce = compile e1 ce +++ compile e2 ce +++ [EQL]
    compileOp Lt  e1 e2 ce = compile e1 ce +++ compile e2 ce +++ [LTH]
  compile (If b tb fb) {t=TipUnit} ce = []
  compile (If b tb fb) {t=TipBool} ce = compile tb ce +++ compile fb ce +++ compile b ce +++ [IF]
  compile (If b tb fb) {t=TipInt} ce = compile tb ce +++ compile fb ce +++ compile b ce +++ [IF]
  compile (App (Lam b) e) ce = compile b (e ::: ce)
  compile (Var stop) {G = x :: xs} (e ::: ce) = compile e ce
  compile (Var (pop k)) (e ::: ce) = compile (Var k) ce
  
---------- Examples ----------

  -- A Expr using most terms compile currently handles
  testExpr : Expr Nil TipInt 
  testExpr = App (Lam (If (OpU Nay (OpB Eql (Var stop) (Val 2))) (OpB Add (Val 2) (Val 3)) (Val 2))) (Val 3)

  -- Compiling testExpr with an empty stack frame
  -- Result with {s=Z}:
  -- [PUSH 2,PUSH 3,ADD,PUSH 2,PUSH 3,PUSH 2,EQL,NAY,IF] : Prog 0 1
  partial
  compileTest : Prog s (S s) 
  compileTest = compile testExpr Nill

  -- Run the compiled program on an empty stack
  -- Result: 
  -- [5] : Vect 1 Int
  partial
  runTestWithEmptyStack : Vect 1 Int 
  runTestWithEmptyStack = run compileTest Vect.Nil

  -- Run the compiled program on a stack with two elements
  -- Result: 
  -- [5,4,9] : Vect 3 Int
  partial
  runTestWithNonEmptyStack : Vect 3 Int 
  runTestWithNonEmptyStack = run compileTest [4,9]

  -- Build a program that requires elements on the stack
  -- Result with {s=Z}:
  -- [ADD] : Prog 2 1
  progWithConsume : Prog (S (S s)) (S s) 
  progWithConsume = [ADD]

  -- Run the above program with sufficient stack
  -- Result:
  -- [5] : Vect 1 Int
  runProgWithConsume : Vect 1 Int 
  runProgWithConsume = run progWithConsume [2,3]

  -- The example below does not type check, because 
  -- progWithConsume requires (S (S s)) elements on 
  -- the stack, and the supplied stack only is of 
  -- size (S Z).
  --
  -- faultyRunProgWithConsume : Vect 1 Int 
  -- faultyRunProgWithConsume = run progWithConsume [3]

