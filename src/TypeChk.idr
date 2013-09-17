module TypeChk
import Interp

%default total

mutual
 data CheckTerm : Type where
   lInf : InfTerm -> CheckTerm
   lLam : CheckTerm -> CheckTerm

 data InfTerm : Type where
   lAnno : CheckTerm -> Tip -> InfTerm -- Annotate a checkable type with a type
   lApp  : InfTerm -> CheckTerm -> InfTerm 
   lVar  : Nat -> InfTerm
   lVal  : Int -> InfTerm
   lOpe  : Char -> InfTerm -> InfTerm -> InfTerm
  
-- data TypeError : Type where
--   typeError : String -> TypeError

makeHasType : (i: Fin n) -> (G: Vect n Tip) -> Maybe (t: Tip ** HasType i G t)
makeHasType fZ     (t :: G) = Just (t ** stop)
makeHasType (fS k) (_ :: G) with (makeHasType k G)
  | Just (_ ** ht) = Just (_ ** pop ht)
  | Nothing        = Nothing

natToFinFromVect : Nat -> Vect n a -> Maybe (Fin n)
natToFinFromVect Z     (_ :: G) = Just fZ
natToFinFromVect (S n) (_ :: G) with (natToFinFromVect n G)
  | Just k  = Just (fS k)
  | Nothing = Nothing
natToFinFromVect _     _        = Nothing

mutual
  check : CheckTerm -> (G: Vect n Tip) -> (t: Tip) -> Maybe (Expr G t)
  check (lInf iterm) G t            = do (t ** expr) <- infer iterm G
                                         return expr
  check (lLam body) G (TipFun t t') = do b <- check body (t :: G) t'
                                         return $ Lam b
  check _ _ _                       = Nothing

  infer : InfTerm -> (G: Vect n Tip) -> Maybe (t: Tip ** Expr G t)
  infer (lAnno cterm t) G = do expr <- check cterm G t
                               return (t ** expr)
  infer (lApp f x) G      = do (TipFun t t' ** f') <- infer f G
                               x'                  <- check x G t
                               return (_ ** App f' x')
  infer (lVar n) G        = do i        <- natToFinFromVect n G
                               (_ ** p) <- makeHasType i G
                               return (_ ** Var p) 
  infer (lVal i) G        = Just (_ ** Val i)
  infer (lOpe op e1 e2) G = case op of -- case expression used here as different operators require different operand types
                                 '+' => do (TipInt ** leftOp)  <- infer e1 G
                                           (TipInt ** rightOp) <- infer e2 G
                                           return (_ ** Ope (+) leftOp rightOp)
  infer _ _               = Nothing


--- Type checking examples ---
-- opTest : Either TypeError Tip
-- opTest = infer (lApp (lAnno (lLam (lLam (lInf (lOpe '+' (lVar 0) (lVar 1))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil

-- appTest : Either TypeError Tip
-- appTest = infer (lAnno (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) (TipFun (TipFun TipInt TipInt) TipInt)) Nil

-- appTest' : Either TypeError Tip
-- appTest' = infer (lAnno (lLam (lLam (lInf (lApp (lVar 0) (lInf (lVar 1)))))) (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt))) Nil
