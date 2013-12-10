module STLC

%default total

mutual
  data Expr : Type where
    Lam  : Expr -> Expr                 -- STLC
    Var  : Nat -> Expr                  -- STLC
    App  : Expr -> Expr -> Expr         -- STLC
    Val  : Int -> Expr                  -- Base type
    Boo  : Bool -> Expr                 -- Base type
    Unit : Expr                         -- Base type
    OpB  : BinOp -> Expr                -- Binary operation
    OpU  : UnOp -> Expr                 -- Unary operation
    Pair : Expr -> Expr -> Expr         -- Product type
    Fst  : Expr -> Expr                 -- Product type
    Snd  : Expr -> Expr                 -- Product type
    InL  : Expr -> Expr                 -- Sum type
    InR  : Expr -> Expr                 -- Sum type
    Case : Expr -> Expr -> Expr -> Expr -- Sum type
    If   : Expr -> Expr -> Expr -> Expr -- Conditional
    Fix  : Expr -> Expr                 -- Recursion

  data BinOp : Type where
    Divide : Expr -> Expr -> BinOp
    Equal  : Expr -> Expr -> BinOp
    Less   : Expr -> Expr -> BinOp 
    Minus  : Expr -> Expr -> BinOp
    Plus   : Expr -> Expr -> BinOp
    Times  : Expr -> Expr -> BinOp

  data UnOp : Type where
    NNot : Expr -> UnOp
