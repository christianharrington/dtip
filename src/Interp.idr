module Interp
import Tip

%default total

interpTip : Tip -> Type
interpTip TipInt  = Int
interpTip TipBool = Bool
interpTip (TipFun T T') = interpTip T -> interpTip T' 

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
    Var  : HasType i G t -> Expr G t
    Val  : (i : Int) -> Expr G TipInt
    Boo  : (b : Bool) -> Expr G TipBool
    Lam  : Expr (t :: G) t' -> Expr G (TipFun t t')
    App  : Expr G (TipFun t t') -> Expr G t -> Expr G t'
    If   : Expr G TipBool -> Expr G t -> Expr G t -> Expr G t
    OpU  : UnOp a b -> Expr G a -> Expr G b 
    OpB  : BinOp a b c -> Expr G a -> Expr G b -> Expr G c      

  data Env : Vect n Tip -> Type where
    Nil  : Env Nil
    (::) : interpTip a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTip t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  partial -- We think it is total, but the totality checker disagrees
  interp : Env G -> Expr G t -> interpTip t
  interp env (Var k)       = lookup k env
  interp env (Val i)       = i
  interp env (Boo b)       = b
  interp env (Lam e)       = \x => interp (x :: env) e
  interp env (App f a)     = interp env f (interp env a)
  interp env (If c t f)    = if interp env c then interp env t else interp env f
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
