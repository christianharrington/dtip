module Interp
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

  data Env : Vect n Tip -> Type where
    Nil  : Env Nil
    (::) : interpTip a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTip t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  partial
  optimize : Expr G t -> Expr G t
  optimize (OpB o e1 e2) = optimizeOp o e1 e2 where
    partial
    optimizeOp : BinOp a b c -> Expr G a -> Expr G b -> Expr G c
    optimizeOp Add e1 e2 = optimizeAddOp e1 e2 where
      partial
      optimizeAddOp : Expr G TipInt -> Expr G TipInt -> Expr G TipInt
      optimizeAddOp (Val a) (Val b)    = Val (a + b)
      optimizeAddOp a       (Val 0)    = optimize a
      optimizeAddOp (Val 0) a          = optimize a
    optimizeOp Sub e1 e2 = optimizeSubOp e1 e2 where
      partial
      optimizeSubOp : Expr G TipInt -> Expr G TipInt -> Expr G TipInt
      optimizeSubOp (Val x) (Val y)    = Val (x - y)
      optimizeSubOp a       (Val 0)    = optimize a
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

  partial -- We think it is total, but the totality checker disagrees
  interp : Env G -> Expr G t -> interpTip t
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
