module InterpR
import Tip

%default total

interpTip : Tip -> Type
interpTip TipUnit        = ()
interpTip TipBool        = Bool
interpTip TipInt         = Int
interpTip (TipProd T T') = (interpTip T, interpTip T')
interpTip (TipSum T T')  = Either (interpTip T) (interpTip T')
interpTip (TipFun T T')  = interpTip T -> interpTip T'
 

using (G: Vect n Tip)
  data HasType : (i : Fin n) -> Vect n Tip -> Tip -> Type where
    stop : HasType fZ (t :: G) t
    pop  : HasType k G t -> HasType (fS k) (u :: G) t 

  data BinOp : Tip -> Tip -> Tip -> Type where
    Add : BinOp TipInt TipInt TipInt
    Sub : BinOp TipInt TipInt TipInt
    Mul : BinOp TipInt TipInt TipInt
    Div : BinOp TipInt TipInt TipInt
    Eql : BinOp TipInt TipInt TipBool
    Lt  : BinOp TipInt TipInt TipBool

  data UnOp : Tip -> Tip -> Type where
    Nay : UnOp TipBool TipBool

  data Expr : Vect n Tip -> Tip -> Type where
    U    : Expr G TipUnit
    Var  : HasType i G t -> Expr G t
    Val  : (i : Int) -> Expr G TipInt
    Boo  : (b : Bool) -> Expr G TipBool
    Lam  : Expr (t :: G) t' -> Expr G (TipFun t t')
    App  : Expr G (TipFun t t') -> Expr G t -> Expr G t'
    If   : Expr G TipBool -> Expr G t -> Expr G t -> Expr G t
    Pair : Expr G a -> Expr G b -> Expr G (TipProd a b)
    Fst  : Expr G (TipProd a b) -> Expr G a
    Snd  : Expr G (TipProd a b) -> Expr G b
    InL  : Expr G a -> (b: Tip) -> Expr G (TipSum a b) -- Inject into left branch
    InR  : Expr G b -> (a: Tip) -> Expr G (TipSum a b) -- Inject into right branch
    Case : Expr G (TipSum a b) -> Expr (a :: G) c -> Expr (b :: G) c -> Expr G c -- Destruct sum type
    OpU  : UnOp a b -> Expr G a -> Expr G b
    OpB  : BinOp a b c -> Expr G a -> Expr G b -> Expr G c
    Fix  : Expr G (TipFun t t) -> Expr G t 

  data Env : Vect n Tip -> Type where
    Nil  : Env Nil
    (::) : interpTip a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTip t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  partial
  optimize : Expr G t -> Expr G t
  -- These are really slow for some reason!
  --optimize (OpB Add (Val x) (Val y)) = Val (x + y)
  --optimize (OpB Add a (Val 0))       = optimize a
  --optimize (OpB Add (Val 0) a)       = optimize a
  --optimize (OpB Sub (Val x) (Val y)) = Val (x - y)
  --optimize (OpB Sub a (Val 0))       = optimize a
  --optimize (OpB Mul (Val x) (Val y)) = Val (x * y)
  --optimize (OpB Mul a (Val 1))       = optimize a
  --optimize (OpB Mul (Val 1) a)       = optimize a
  --optimize (OpB Div (Val x) (Val y)) = Val (cast ((cast x) / (cast y)))
  --optimize (OpB Div a (Val 1))       = optimize a
  --optimize (OpB o   a       b)       = OpB o (optimize a) (optimize b)
  optimize (Lam e)                   = Lam (optimize e)
  optimize (OpU Nay (OpU Nay a))     = optimize a
  optimize (OpU o   a)               = OpU o (optimize a)
  optimize (If (Boo True)  b1 b2)    = optimize b1
  optimize (If (Boo False) b1 b2)    = optimize b2
  optimize (If  c   b1     b2)       = If (optimize c) (optimize b1) (optimize b2)
  optimize (Fst p)                   = Fst (optimize p)
  optimize (Snd p)                   = Snd (optimize p)
  optimize (Pair    fst    snd)      = Pair (optimize fst) (optimize snd)
  optimize a                         = a

  data Value : (G: Vect n Tip) -> Expr G t -> Type where
    V_Unit : Value G U
    V_Int  : Value G (Val i)
    V_Bool : Value G (Boo b)
    V_Lam  : (b: Expr (t :: G) t') -> Value G (Lam b) -- Note: body does not need to be a value
    V_Pair : {a: Expr G t} -> {b: Expr G t'} -> Value G a -> Value G b -> Value G (Pair a b)
    V_InL  : {a: Expr G t} -> Value G a -> (b: Tip) -> Value G (InL a b)
    V_InR  : {b: Expr G t} -> Value G b -> (a: Tip) -> Value G (InR b a)

  using(G': Vect m Tip)

    splitVar : {G: Vect m Tip} -> {G': Vect n Tip} -> HasType i (G ++ G') t -> Either (Exists (Fin m) (\k => HasType k G t)) (Exists (Fin n) (\k => HasType k G' t))
    splitVar {m = Z}    {G=[]}   {i=i}    x       = Right (i ** x)
    splitVar {m = S m'} {G=t::G} {i=fZ}   stop    = Left (fZ ** stop)
    splitVar {m = S m'} {G=u::G}          (pop x) with (splitVar x)
      | Left (i' ** x')  = Left (fS i' ** pop x')
      | Right (i' ** x') = Right (i' ** x')

    data SnocView : Vect n a -> Type where
      sNil : {a: Type} -> SnocView {a=a} Nil
      Snoc : (xs: Vect n a) -> (x: a) -> SnocView (xs ++ [x])

    snoc : (xs: Vect n a) -> SnocView xs
    snoc [] = sNil
    snoc (x :: xs) with (snoc xs)
     snoc (x :: []) | sNil = Snoc Nil x
     snoc (x :: (ys ++ [y])) | Snoc ys y = Snoc (x :: ys) y

    weakenN : (i : Fin n) -> (m: Nat) -> Fin (n + m)
    weakenN {n=n} i Z = rewrite plusZeroRightNeutral n in i
    weakenN {n=n} i (S m') = rewrite sym (plusSuccRightSucc n m') in weaken (weakenN i m')


    dreplace : {i : Type} -> {a : i -> Type} -> {s : i} -> {r : i} -> 
               (x : a s) -> (y : a r) -> (P : (t : i) -> a t -> Type) ->
               x = y -> P _ x -> P _ y 
    dreplace x x P refl p = p 
  
    vnil_lemma : (xs : Vect n a) -> xs = (xs ++ []) 
    vnil_lemma [] = refl 
    vnil_lemma {a} (x :: xs) = let ih = vnil_lemma xs in dreplace {a = \n => Vect n a} xs (xs ++ []) (\n, v : Vect n a => x :: xs = x :: v) ih refl

    -- hasTypeAppendNil : (G: Vect n Tip) -> (G = G++[]) -> (x: HasType i G t) -> (y: HasType i (G++[]) t) -> x = (dreplace {a=\G => HasType i G t} G (G++[]) (\G, z: HasType i G t => x = z) (vnil_lemma G) x)
    -- hasTypeAppendNil [] x y = dreplace {a=\G => HasType i G t} [] ([]++[]) (\G, z: HasType i G t => x = z) (vnil_lemma []) x
    -- hasTypeAppendNil (x::xs) x y = ?hatn

    --vassoc_lemma : (xs: Vect m a) -> (ys: Vect n a) -> (zs: Vect o a) -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
    --vassoc_lemma [] ys xs = refl
    --vassoc_lemma {a} (x :: xs) ys zs = let ih = vassoc_lemma xs ys zs in dreplace {a = \n => Vect n a} (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
    --                                                                              (\n, v : Vect n a => ((x::xs)++(ys++zs)) = (((x :: v)++ys)++zs)) ih refl

    append' : {i: Fin n} -> {G: Vect n Tip} -> HasType i G t -> (t': Tip) -> Exists (Fin (n+1)) (\k => HasType k (G ++ [t']) t)
    append' {i=fZ} stop t' = (fZ ** stop)
    append' (pop x) t' with (append' x t')
      | (k ** x') = (fS k ** pop x')

    appendNil : {i: Fin n} -> {G: Vect n Tip} -> HasType i G t -> Exists (Fin (n+0)) (\k => HasType k (G++[]) t)
    appendNil {i=fZ} stop = (fZ ** stop)
    appendNil (pop x) with (appendNil x)
      | (k ** x') = (fS k ** pop x')

    append : {E: Vect m Tip} -> HasType i E t -> (G: Vect n Tip) -> Exists (Fin (m+n)) (\k => HasType k (E ++ G) t)
    append {E=E} {i=i} x [] = appendNil x
    append x (t' :: G') = let (k ** x') = append' x t' in append x' G' 

    prepend : {G: Vect n Tip} -> HasType i G t -> (E: Vect m Tip) -> Exists (Fin (m+n)) (\k => HasType k (E ++ G) t)
    prepend {i=i} x [] = (i ** x)
    prepend x ts with (snoc ts)
      prepend x [] | sNil = prepend x []
      prepend x (ys ++ [y]) | Snoc ys y = prepend (pop {u=y} x) ys

    weakenHasType : {E: Vect m Tip, G: Vect n Tip} -> HasType i (E ++ G) t -> (F: Vect o Tip) -> Exists (Fin (m+o+n)) (\k => HasType k (E ++ F ++ G) t)
    weakenHasType {m=m} {n=n} {o=o} {E=E} {G=G} x F = case splitVar x of
                                                        Left (k ** x')  => let (k' ** x'') = append x' F  in append x'' G
                                                        Right (k ** x') => let (k' ** x'') = prepend x' F in prepend x'' E


    weaken : {E: Vect m Tip, G: Vect n Tip} -> (F: Vect o Tip) -> Expr (E ++ G) t -> Expr (E ++ F ++ G) t
    weaken F U = U 
    weaken F (Val i) = Val i
    weaken F (Boo b) = Boo b
    weaken F (Var x) = let (k ** x') = weakenHasType x F in Var x'
    weaken {t=TipFun x y} {E=E} F (Lam b) = Lam $ weaken {E=x::E} F b
    weaken F (App f v) = App (weaken F f) (weaken F v)
    weaken F (If c tb fb) = If (weaken F c) (weaken F tb) (weaken F fb)
    weaken F (Pair a b) = Pair (weaken F a) (weaken F b)
    weaken F (Fst p) = Fst $ weaken F p
    weaken F (Snd p) = Snd $ weaken F p
    weaken F (InL a b) = InL (weaken F a) b
    weaken F (InR b a) = InR (weaken F b) a
    weaken F {E=E} (Case {a=a} {b=b} s l r) = Case (weaken F s) (weaken {E=a::E} F l) (weaken {E=b::E} F r)
    weaken F (OpU o a) = OpU o $ weaken F a
    weaken F (OpB o a b) = OpB o (weaken F a) (weaken F b)
    weaken F (Fix f) = Fix $ weaken F f


    --partial
    --weakenR : (G': Vect m Tip) -> Expr G t -> Expr (G ++ G') t

    substGlobal : {Gglob : Vect (S n) Tip} -> HasType i Gglob t -> HasType fZ Gglob t' -> Expr (tail Gglob) t' -> Expr (tail Gglob) t
    substGlobal stop    stop v = v
    substGlobal (pop x) stop v = Var x

    subst : {Gglob : Vect (S n) Tip} -> {Glam: Vect m Tip} -> (e: Expr (Glam ++ Gglob) t) -> HasType fZ Gglob t' -> (v: Expr (tail Gglob) t') -> Expr (Glam ++ (tail Gglob)) t
    subst U i v = U
    subst (Val i') i v = Val i'
    subst (Boo b) i v = Boo b
    subst {Glam=Glam} {Gglob=Gglob} (Var y) i v = case splitVar y of
                                                    Left (k ** y')  => let (k' ** y'') = appendNil y' in
                                                                        weaken {E=Glam} {G=[]} (tail Gglob) (Var y'') -- Extend env of y' with Gglob
                                                    Right (k ** y') => weaken {E=[]} Glam (substGlobal y' i v) -- v or tail y'
    subst {Glam=Glam} {t=TipFun x y} (Lam b) i v = Lam $ subst {Glam = x :: Glam} b i v
    subst (App f x) i v = App (subst f i v) (subst x i v)
    subst (If c tb fb) i v = If (subst c i v) (subst tb i v) (subst fb i v)
    subst (Pair a b) i v = Pair (subst a i v) (subst b i v)
    subst (Fst p) i v = Fst (subst p i v)
    subst (Snd p) i v = Snd (subst p i v)
    subst (InL a b) i v = InL (subst a i v) b
    subst (InR b a) i v = InR (subst b i v) a
    subst {Glam=Glam} (Case {a=a} {b=b} s l r) i v = Case (subst s i v) (subst {Glam=a::Glam} l i v) (subst {Glam=b::Glam} r i v)
    subst (OpU o a) i v = OpU o (subst a i v)
    subst (OpB o a b) i v = OpB o (subst a i v) (subst b i v)
    subst (Fix f) i v = Fix (subst f i v)


    data Step : Expr G t -> Expr G' t -> Type where
      S_App1    : {t1: Expr G (TipFun t t'), t1': Expr G (TipFun t t'), t2: Expr G t} ->
                  Step t1 t1' ->
                  Step (App t1 t2) (App t1' t2)
      S_App2    : {t2: Expr G t, t2': Expr G t, f: Expr G (TipFun t t')} ->
                  Value G f ->
                  Step t2 t2' ->
                  Step (App f t2) (App f t2')
--      S_AppBeta : {v: Expr G t, b: Expr (t :: G) t', b': Expr G t'} ->
--                  Value G v ->
                  --Subst stop v b b' ->
 --                 Step (App (Lam b) v) (subst b stop v) -- App (Lam b) v -> {Var stop -> v} b
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
                  Value G a ->
                  Step b b' -> 
                  Step (Pair a b) (Pair a b')
      S_Fst     : {p: Expr G (TipProd a b), p': Expr G (TipProd a b)} ->
                  Step p p' ->
                  Step (Fst p) (Fst p')
      S_Snd     : {p: Expr G (TipProd a b), p': Expr G (TipProd a b)} ->
                  Step p p' -> 
                  Step (Snd p) (Snd p')
      S_FstBeta : {a: Expr G t, b: Expr G t'} ->
                  Value G a ->
                  Step (Fst (Pair a b)) a
      S_SndBeta : {a: Expr G t, b: Expr G t'} ->
                  Value G b -> 
                  Step (Snd (Pair a b)) b
      -- Sum
      S_Case    : {s: Expr G (TipSum a b), s': Expr G (TipSum a b), l: Expr (a :: G) c, r: Expr (b :: G) c} ->
                  Step s s' ->
                  Step (Case s l r) (Case s' l r)
      S_CaseInL : {e: Expr G a, l: Expr (a :: G) c, r: Expr (b :: G) c} ->
                  Value (a :: G) l ->
                  Step (Case (InL e b) l r) l
      S_CaseInR : {e: Expr G b, l: Expr (a :: G) c, r: Expr (b :: G) c} ->
                  Value (b :: G) r ->
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
--      S_FixBeta : {b: Expr (t :: G) t, b': Expr G t} ->
                  --Subst stop (Fix (Lam b)) b b' ->
--                  Step (Fix (Lam b)) (subst b stop (Fix (Lam b)))
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



    testStep : Step {G = Nil} {G' = Nil} (App (Lam (Var (stop))) (Val 5)) (Val 5)
    testStep = ?test --S_AppAbs V_Int (Sub_Var1)
    
    using (G'': Vect o Tip) -- Inspired by SfLib
      data MultiStep : Expr G t -> Expr G' t -> Type where
         Multi_Refl : {a: Expr G t} -> MultiStep a a
         Multi_Step : {a: Expr G t, b: Expr G' t, c: Expr G'' t} -> 
                      Step a b -> MultiStep b c -> MultiStep a c

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

    testFact : MultiStep {G = Nil} {G' = Nil} (App fact (Val 3)) (Val 6)
    testFact = ?testfact
    

  partial -- We think it is total, but the totality checker disagrees
  interp : Env G -> Expr G t -> interpTip t
  interp env U             = ()
  interp env (Var k)       = lookup k env
  interp env (Val i)       = i
  interp env (Boo b)       = b
  interp env (Lam e)       = \x => interp (x :: env) e
  interp env (App f a)     = interp env f (interp env a)
  interp env (If c t f)    = if interp env c then interp env t else interp env f
  interp env (Pair a b)    = (interp env a, interp env b)
  interp env (Fst p)       = fst (interp env p)
  interp env (Snd p)       = snd (interp env p)
  interp env (InL a t)     = Left (interp env a)
  interp env (InR b t)     = Right (interp env b)
  interp env (Case o a b)  = case (interp env o) of
                                  Left l  => interp (l :: env) a
                                  Right r => interp (r :: env) b
  interp env (OpB Add a b) = (interp env a) + (interp env b)
  interp env (OpB Sub a b) = (interp env a) - (interp env b)
  interp env (OpB Mul a b) = (interp env a) * (interp env b)
  interp env (OpB Div a b) = (cast ((cast (interp env a)) / (cast (interp env b))))
  interp env (OpB Eql a b) = (interp env a) == (interp env b)
  interp env (OpB Lt  a b) = (interp env a) < (interp env b)
  interp env (OpU Nay a)   = not (interp env a)
 
  dsl expr
    lambda      = Lam
    variable    = Var
    index_first = stop
    index_next  = pop

---------- Examples ----------
  val : Expr Nil TipInt
  val = Val 0

  lam : Expr Nil (TipFun TipInt TipInt)
  lam = expr (\x => x)

  add' : Expr Nil (TipFun TipInt (TipFun TipInt TipInt))
  add' = expr (\x => (\y => OpB Add x y))



