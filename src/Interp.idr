module Interp
import Tip
import Decidable.Decidable
import Decidable.Equality

%default total

interpTip : Tip -> Type
interpTip TipInt  = Int
interpTip TipBool = Bool
interpTip (TipFun T T') = interpTip T -> interpTip T'

using (G: Vect n Tip)
  data HasType : (i : Fin n) -> Vect n Tip -> Tip -> Type where
    stop : HasType fZ (t :: G) t
    pop  : HasType k G t -> HasType (fS k) (u :: G) t 

  data Expr : Vect n Tip -> Tip -> Type where
    Var : HasType i G t -> Expr G t
    Val : (i : Int) -> Expr G TipInt
    Lam : Expr (t :: G) t' -> Expr G (TipFun t t')
    App : Expr G (TipFun t t') -> Expr G t -> Expr G t'
    Ope : (interpTip a -> interpTip b -> interpTip c) -> Expr G a -> Expr G b -> Expr G c

  data Env : Vect n Tip -> Type where
    Nil  : Env Nil
    (::) : interpTip a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTip t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  interp : Env G -> Expr G t -> interpTip t
  interp env (Var k)     = lookup k env
  interp env (Val i)     = i
  interp env (Lam e)     = \x => interp (x :: env) e
  interp env (App f a)   = interp env f (interp env a)
  interp env (Ope f a b) = f (interp env a) (interp env b)

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
  add' = expr (\x => (\y => Ope (+) x y))
