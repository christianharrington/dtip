module STLC

%default total

mutual
  data Expr : Type where
    App  : Expr -> Expr -> Expr
    Boo  : Bool -> Expr
    Case : Expr -> Expr -> Expr -> Expr
    Fix  : Expr -> Expr
    Fst  : Expr -> Expr
    If   : Expr -> Expr -> Expr -> Expr
    InL  : Expr -> Expr
    InR  : Expr -> Expr
    Lam  : Expr -> Expr
    OpB  : BinOp -> Expr
    OpU  : UnOp -> Expr
    Pair : Expr -> Expr -> Expr
    Snd  : Expr -> Expr
    Unit : Expr
    Val  : Int -> Expr
    Var  : Nat -> Expr

  data BinOp : Type where
    Divide : Expr -> Expr -> BinOp
    Equal  : Expr -> Expr -> BinOp
    Less   : Expr -> Expr -> BinOp 
    Minus  : Expr -> Expr -> BinOp
    Plus   : Expr -> Expr -> BinOp
    Times  : Expr -> Expr -> BinOp

  data UnOp : Type where
    NNot : Expr -> UnOp
