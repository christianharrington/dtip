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
   lOpe  : BinOp -> InfTerm

 data BinOp : Type where
   Plus  : InfTerm -> InfTerm -> BinOp
  
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

-- If t and t' are equal, we can exchange t' for t in the Expr argument
exprTipEqSwap : (t: Tip) -> (t': Tip) -> (G: Vect n Tip) -> (p: Dec (t = t')) -> Expr G t -> Maybe (Expr G t')
exprTipEqSwap t t' G (Yes p) e = Just ?exprTipEqSwapYescase
exprTipEqSwap t t' G (No  p) e = Nothing

mutual
  partial
  check : CheckTerm -> (G: Vect n Tip) -> (t: Tip) -> Maybe (Expr G t)
  check (lInf iterm) G t            = do (t' ** e) <- infer iterm G
                                         expr <- exprTipEqSwap t' t G (decEq t' t) e
                                         return expr
  check (lLam body) G (TipFun t t') = do b <- check body (t :: G) t'
                                         return $ Lam b
  check _ _ _                       = Nothing

  partial
  infer : InfTerm -> (G: Vect n Tip) -> Maybe (t: Tip ** Expr G t)
  infer (lAnno cterm t) G = do expr <- check cterm G t
                               return (_ ** expr)
  infer (lApp f x) G      = do (TipFun t t' ** f') <- infer f G
                               x'                  <- check x G t
                               return (_ ** App f' x')
  infer (lVar n) G        = do i        <- natToFinFromVect n G
                               (_ ** p) <- makeHasType i G
                               return (_ ** Var p) 
  infer (lVal i) G        = Just (_ ** Val i)
  infer (lOpe op) G       = case op of -- case expression used here as different operators require different operand types
                                 Plus e1 e2 => do (TipInt ** leftOp)  <- infer e1 G
                                                  (TipInt ** rightOp) <- infer e2 G
                                                  return (_ ** Ope (+) leftOp rightOp)
                                 _          => Nothing
  infer _ _               = Nothing


--- Type checking examples ---
using (G: Vect n Tip)
  partial
  opTest : Maybe (t: Tip ** Expr Nil t)
  opTest =  infer (lApp (lAnno (lLam (lLam (lInf (lOpe (Plus (lVar 1) (lVar 0)))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil
  
  partial
  opTestNeg : Maybe (t: Tip ** Expr Nil t)
  opTestNeg =  infer (lApp (lAnno (lLam (lLam (lInf (lOpe (Plus (lVar 1) (lVar 0)))))) (TipFun TipBool (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil

  partial
  valTest : Maybe (t: Tip ** Expr Nil t)
  valTest = infer (lVal 10) Nil

  partial
  idTest : Maybe (t: Tip ** Expr Nil t)
  idTest = infer (lAnno (lLam (lInf (lVar 0))) (TipFun TipInt TipInt)) Nil

  partial
  idTestNeg : Maybe (t: Tip ** Expr Nil t)
  idTestNeg = infer (lAnno (lLam (lInf (lVar 0))) TipInt) Nil

  partial
  appTest : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) TipInt))
  appTest = check (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) Nil (TipFun (TipFun TipInt TipInt) TipInt)

  partial
  appTest' : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt)))
  appTest' = check (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt))

-- appTest' : Either TypeError Tip
-- appTest' = infer (lAnno (lLam (lLam (lInf (lApp (lVar 0) (lInf (lVar 1)))))) (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt))) Nil

---------- Proofs ----------

TypeChk.exprTipEqSwapYescase = proof {
  intros;
  rewrite p;
  trivial;
}
