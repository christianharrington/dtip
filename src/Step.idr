module Step
import Interp

%default total

using (G: Vect n Tip)
  data NormalForm : (G: Vect n Tip) -> Expr G t -> Type where
    NF_Unit : NormalForm G U
    NF_Int  : NormalForm G (Val i)
    NF_Bool : NormalForm G (Boo b)
    NF_Lam  : {b: Expr (t :: G) t'} -> NormalForm G (Lam b) -- Note: body does not need to be a value
    NF_Pair : {a: Expr G t} -> {b: Expr G t'} -> NormalForm G a -> NormalForm G b -> NormalForm G (Pair a b)
    NF_InL  : {a: Expr G t} -> NormalForm G a -> (b: Tip) -> NormalForm G (InL a b)
    NF_InR  : {b: Expr G t} -> NormalForm G b -> (a: Tip) -> NormalForm G (InR b a)

  splitVar : {G: Vect m Tip} -> {G': Vect n Tip} -> HasType i (G ++ G') t -> Either (k: Fin m ** HasType k G t) (k: Fin n ** HasType k G' t)
  splitVar {m = Z}    {G=[]}   {i=i}    x       = Right (i ** x)
  splitVar {m = S m'} {G=t::G} {i=fZ}   stop    = Left (fZ ** stop)
  splitVar {m = S m'} {G=u::G}          (pop x) with (splitVar x)
    | Left (i' ** x')  = Left (fS i' ** pop x')
    | Right (i' ** x') = Right (i' ** x')

  weakenN : (n : Nat) -> (m : Nat) -> Fin n -> Fin (n + m)
  weakenN (S n) m fZ = fZ
  weakenN (S n) m (fS f) = fS (weakenN n m f)

  append : {E: Vect m Tip} -> HasType i E t -> (G: Vect n Tip) -> HasType (weakenN m n i) (E ++ G) t
  append stop G = stop
  append (pop ht) G = pop (append ht G)

  shiftFin : (m : Nat) -> Fin n -> Fin (m + n)
  shiftFin Z f = f
  shiftFin {n=n} (S m) f = fS {k = (m + n)} (shiftFin m f)

  prepend : {G: Vect n Tip} -> HasType i G t -> (E: Vect m Tip) -> HasType (shiftFin m i) (E ++ G) t
  prepend ht [] = ht
  prepend ht (t::ts) = pop (prepend ht ts)

  weaken : {E: Vect m Tip, G: Vect n Tip} -> (F: Vect o Tip) -> Expr (E ++ G) t -> Expr (E ++ F ++ G) t
  weaken F U = U 
  weaken F (Val i) = Val i
  weaken F (Boo b) = Boo b
  weaken {E} {G} F (Var x) = case splitVar x of
                               Left (k ** x') => Var $ append (append x' F) G
                               Right (k ** x') => Var $ prepend x' (E++F)
  weaken {t=TipFun x y} {E=E} F (Lam b) = Lam $ weaken {E=x::E} F b
  weaken F (App f v) = App (weaken F f) (weaken F v)
  weaken F (If c tb fb) = If (weaken F c) (weaken F tb) (weaken F fb)
  weaken F (Pair a b) = Pair (weaken F a) (weaken F b)
  weaken F (Fst p) = Fst $ weaken F p
  weaken F (Snd p) = Snd $ weaken F p
  weaken F (InL a b) = InL (weaken F a) b
  weaken F (InR b a) = InR (weaken F b) a
  weaken F {E} (Case {a} {b} s l r) = Case (weaken F s) (weaken {E=a::E} F l) (weaken {E=b::E} F r)
  weaken F (OpU o a) = OpU o $ weaken F a
  weaken F (OpB o a b) = OpB o (weaken F a) (weaken F b)
  weaken F (Fix f) = Fix $ weaken F f

  -- Substitute global variable
  substGlobal : {Gglob : Vect (S n) Tip} -> HasType i Gglob t -> HasType fZ Gglob t' -> Expr (tail Gglob) t' -> Expr (tail Gglob) t
  substGlobal stop    stop v = v
  substGlobal (pop x) stop v = Var x

  subst : {Gglob : Vect (S n) Tip} -> {Glam: Vect m Tip} -> (e: Expr (Glam ++ Gglob) t) -> HasType fZ Gglob t' -> (v: Expr (tail Gglob) t') -> Expr (Glam ++ (tail Gglob)) t
  subst U i v = U
  subst (Val i') i v = Val i'
  subst (Boo b) i v = Boo b
  subst {Glam} {Gglob} (Var y) i v = case splitVar y of
                                       Left (k ** y')  => Var $ append y' (tail Gglob) -- Local var: Extend env of y' with Gglob
                                       Right (k ** y') => weaken {E=[]} Glam (substGlobal y' i v) -- v or tail y'
  subst {Glam} {t=TipFun x y} (Lam b) i v = Lam $ subst {Glam = x :: Glam} b i v
  subst (App f x) i v = App (subst f i v) (subst x i v)
  subst (If c tb fb) i v = If (subst c i v) (subst tb i v) (subst fb i v)
  subst (Pair a b) i v = Pair (subst a i v) (subst b i v)
  subst (Fst p) i v = Fst (subst p i v)
  subst (Snd p) i v = Snd (subst p i v)
  subst (InL a b) i v = InL (subst a i v) b
  subst (InR b a) i v = InR (subst b i v) a
  subst {Glam} (Case {a} {b} s l r) i v = Case (subst s i v) (subst {Glam = a :: Glam} l i v) (subst {Glam = b :: Glam} r i v)
  subst (OpU o a) i v = OpU o (subst a i v)
  subst (OpB o a b) i v = OpB o (subst a i v) (subst b i v)
  subst (Fix f) i v = Fix (subst f i v)

  using (G': Vect m Tip)
    data Step : Expr G t -> Expr G' t -> Type where
      S_App1    : {t1: Expr G (TipFun t t'), t1': Expr G (TipFun t t'), t2: Expr G t} ->
                  Step t1 t1' ->
                  Step (App t1 t2) (App t1' t2)
      S_App2    : {t2: Expr G t, t2': Expr G t, f: Expr G (TipFun t t')} ->
                  NormalForm G f ->
                  Step t2 t2' ->
                  Step (App f t2) (App f t2')
      S_AppBeta : {v: Expr G t, b: Expr (t :: G) t', b': Expr G t'} ->
                  NormalForm G v ->
                  Step (App (Lam b) v) (subst {Glam=[]} b stop v) -- App (Lam b) v -> {Var stop -> v} b
      -- If
      S_IfCond  : {c: Expr G TipBool, c': Expr G TipBool, tb: Expr G t, fb: Expr G t} ->
                  Step c c' ->
                  Step (If c tb fb) (If c' tb fb)
      S_IfTrue  : {tb: Expr G t, fb: Expr G t} ->
                  Step (If (Boo True) tb fb) tb
      S_IfFalse : {tb: Expr G t, fb: Expr G t} ->
                  Step (If (Boo False) tb fb) fb
      -- Product
      S_Pair1   : {a: Expr G t, a': Expr G t, b: Expr G t'} ->
                  Step a a' ->
                  Step (Pair a b) (Pair a' b)
      S_Pair2   : {a: Expr G t, b: Expr G t', b': Expr G t'} ->
                  NormalForm G a ->
                  Step b b' -> 
                  Step (Pair a b) (Pair a b')
      S_Fst     : {p: Expr G (TipProd a b), p': Expr G (TipProd a b)} ->
                  Step p p' ->
                  Step (Fst p) (Fst p')
      S_Snd     : {p: Expr G (TipProd a b), p': Expr G (TipProd a b)} ->
                  Step p p' -> 
                  Step (Snd p) (Snd p')
      S_FstBeta : {a: Expr G t, b: Expr G t'} ->
                  NormalForm G a ->
                  Step (Fst (Pair a b)) a
      S_SndBeta : {a: Expr G t, b: Expr G t'} ->
                  NormalForm G b -> 
                  Step (Snd (Pair a b)) b
      -- Sum
      S_Case    : {s: Expr G (TipSum a b), s': Expr G (TipSum a b), l: Expr (a :: G) c, r: Expr (b :: G) c} ->
                  Step s s' ->
                  Step (Case s l r) (Case s' l r)
      S_CaseInL : {e: Expr G a, l: Expr (a :: G) c, r: Expr (b :: G) c} ->
                  NormalForm (a :: G) l ->
                  Step (Case (InL e b) l r) l
      S_CaseInR : {e: Expr G b, l: Expr (a :: G) c, r: Expr (b :: G) c} ->
                  NormalForm (b :: G) r ->
                  Step (Case (InR e a) l r) r
      S_InL     : {e: Expr G a, e': Expr G' a} ->
                  Step e e' ->
                  Step (InL e b) (InL e' b)
      S_InR     : {e: Expr G b, e': Expr G' b} -> 
                  Step e e' ->
                  Step (InR e a) (InR e' a)
      -- Fix
      S_Fix    : {f: Expr G (TipFun t t), f': Expr G' (TipFun t t)} ->
                 Step f f' ->
                 Step (Fix f) (Fix f')
      S_FixBeta : {b: Expr (t :: G) t, b': Expr G t} ->
                  Step (Fix (Lam b)) (subst {Glam=[]} b stop (Fix (Lam b)))
      -- Operators
      S_Add1    : {e1: Expr G TipInt, e1': Expr G TipInt, e2: Expr G TipInt} ->
                  Step e1 e1' ->
                  Step (OpB Add e1 e2) (OpB Add e1' e2)
      S_Add2    : {e2: Expr G TipInt, e2': Expr G' TipInt} ->
                  Step e2 e2' ->
                  Step (OpB Add (Val i) e2) (OpB Add (Val i) e2')
      S_Add     : Step (OpB Add (Val {G = G} a) (Val {G = G} b)) (Val {G = G} (a + b))
      S_Sub1    : {e1: Expr G TipInt, e1': Expr G TipInt, e2: Expr G TipInt} ->
                  Step e1 e1' ->
                  Step (OpB Sub e1 e2) (OpB Sub e1' e2)
      S_Sub2    : {e2: Expr G TipInt, e2': Expr G' TipInt} ->
                  Step e2 e2' ->
                  Step (OpB Sub (Val i) e2) (OpB Sub (Val i) e2')
      S_Sub     : Step (OpB Sub (Val {G = G} a) (Val {G = G} b)) (Val {G = G} (a - b))
      S_Mul1    : {e1: Expr G TipInt, e1': Expr G TipInt, e2: Expr G TipInt} ->
                  Step e1 e1' ->
                  Step (OpB Mul e1 e2) (OpB Mul e1' e2)
      S_Mul2    : {e2: Expr G TipInt, e2': Expr G' TipInt} ->
                  Step e2 e2' ->
                  Step (OpB Mul (Val i) e2) (OpB Mul (Val i) e2')
      S_Mul     : Step (OpB Mul (Val {G = G} a) (Val {G = G} b)) (Val {G = G} (a * b))
      S_Eql1    : {e1: Expr G TipInt, e1': Expr G TipInt, e2: Expr G TipInt} ->
                  Step e1 e1' ->
                  Step (OpB Eql e1 e2) (OpB Eql e1' e2)
      S_Eql2    : {e2: Expr G TipInt, e2': Expr G' TipInt} ->
                  Step e2 e2' ->
                  Step (OpB Eql (Val i) e2) (OpB Eql (Val i) e2')
      S_Eql     : Step (OpB Eql (Val {G = G} a) (Val {G = G} b)) (Boo {G = G} (a == b))

    using (G'': Vect o Tip) -- Inspired by SfLib
      data MultiStep : Expr G t -> Expr G' t -> Type where
         M_Refl : {a: Expr G t} -> MultiStep a a
         M_Step : {a: Expr G t, b: Expr G' t, c: Expr G'' t} -> 
                  Step a b -> MultiStep b c -> MultiStep a c

  testStep : Step {G = Nil} {G' = Nil} (App (Lam (Var (stop))) (Val 5)) (Val 5)
  testStep = ?test --S_AppAbs V_Int (Sub_Var1)

  testStepIf : Step {G = Nil} {G' = Nil} (App (Lam (If (Var stop) (Val 1) (Val 0))) (Boo True)) (If (Boo True) (Val 1) (Val 0))
  testStepIf = ?testif

  testMultiStepIf : MultiStep {G = Nil} {G' = Nil} (App (Lam (If (Var stop) (Val 1) (Val 0))) (Boo True)) (Val 1)
  testMultiStepIf = ?testmulti

  fact : Expr G (TipFun TipInt TipInt)
  fact = Fix (Lam 
               (Lam 
                  (If (OpB Eql (Val 0) (Var stop)) -- if x == 0
                    (Val 1) -- then 1
                    (OpB Mul (Var stop) (App (Var (pop stop)) (OpB Sub (Var stop) (Val 1))))))) -- else (x * f (x - 1))

  testFact : MultiStep {G = Nil} {G' = Nil} (App Step.fact (Val 1)) (Val 1)
  testFact = ?testfact

  sub_slowly : Expr G (TipFun TipInt TipInt)
  sub_slowly = Fix (Lam (Lam (If (OpB Eql (Var stop) (Val 0))
                                 (Val 0)
                                 ((App (Var (pop stop)) (OpB Sub (Var stop) (Val 1)))))))


  sub_three : MultiStep {G = Nil} {G' = Nil} (App sub_slowly (Val 3)) (Val 0)
  sub_three = ?st

  forever : Expr G (TipFun TipInt TipInt)
  forever = Fix (Lam (Lam (If (OpB Eql (Var stop) (Val 1))
                              (App (Var (pop stop)) (Val 1))
                              (Val 0))))

  testForever : MultiStep {G = Nil} {G' = Nil} (App Step.forever (Val 1)) (Val 0)
  testForever = ?fe




---------- Proofs ----------

Step.st = proof
  refine M_Step
  refine S_App1
  refine S_FixBeta
  refine M_Step
  refine S_AppBeta
  refine NF_Int
  refine M_Step
  refine S_IfCond
  refine S_Eql
  refine M_Step
  refine S_IfFalse
  refine M_Step
  refine S_App1
  refine S_FixBeta
  refine M_Step
  refine S_App2
  refine NF_Lam
  refine S_Sub
  refine M_Step
  refine S_AppBeta
  refine NF_Int
  refine M_Step
  refine S_IfCond
  refine S_Eql
  refine M_Step
  refine S_IfFalse
  refine M_Step
  refine S_App1
  refine S_FixBeta
  refine M_Step
  refine S_App2
  refine NF_Lam
  refine S_Sub
  refine M_Step
  refine S_AppBeta
  refine NF_Int
  refine M_Step
  refine S_IfCond
  refine S_Eql
  refine M_Step
  refine S_IfFalse
  refine M_Step
  refine S_App1
  refine S_FixBeta
  refine M_Step
  refine S_App2
  refine NF_Lam
  refine S_Sub
  refine M_Step
  refine S_AppBeta
  refine NF_Int
  refine M_Step
  refine S_IfCond
  refine S_Eql
  refine M_Step
  refine S_IfTrue
  refine M_Refl
  refine sub_slowly
  exact (Val 3)
  refine sub_slowly
  exact (Val 2)
  refine sub_slowly
  exact (Val 1)
  refine sub_slowly
  exact (Val 0)


Step.testif = proof
  refine S_AppBeta
  refine NF_Bool
  exact (Val 1)


Step.testfact = proof
  refine M_Step
  refine S_App1
  refine S_FixBeta
  refine M_Step
  refine S_AppBeta
  refine NF_Int
  refine M_Step
  refine S_IfCond
  refine S_Eql
  refine M_Step
  refine S_IfFalse
  refine M_Step
  refine S_Mul2
  refine S_App1
  refine S_FixBeta
  refine M_Step
  refine S_Mul2
  refine S_App2
  refine NF_Lam
  refine S_Sub
  refine M_Step
  refine S_Mul2
  refine S_AppBeta
  refine NF_Int
  refine M_Step
  refine S_Mul2
  refine S_IfCond
  refine S_Eql
  refine M_Step
  refine S_Mul2
  refine S_IfTrue
  refine M_Step
  refine S_Mul
  refine M_Refl
  refine Step.fact
  exact (Val 1)
  refine Step.fact
  exact (Val 1)


