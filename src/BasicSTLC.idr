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
                                         expr <- exprTipEqSwap t' t G (decEq t' t) e -- Swap t with t'
                                         return expr
  check (lLam body) G (TipFun t t') = do b <- check body (t :: G) t'
                                         return $ Lam b
  check _ _ _                       = Nothing

  partial
  infer : InfTerm -> (G: Vect n Tip) -> Maybe (t: Tip ** Expr G t)
  infer (lAnno cterm t) G = do expr <- check cterm G t
                               return (_ ** expr)
  infer (lApp f x) G      = do (TipFun t t' ** f') <- infer f G -- Should probably fail more gracefully
                               x'                  <- check x G t
                               return (_ ** App f' x')
  infer (lVar n) G        = do i        <- natToFinFromVect n G
                               (_ ** p) <- makeHasType i G
                               return (_ ** Var p) 
  infer (lVal i) G        = Just (_ ** Val i)
  infer (lOpe op) G       = case op of -- case expression used here as different operators require different operand types
                                 Plus e1 e2 => do (TipInt ** leftOp)  <- infer e1 G -- Should probably fail more gracefully
                                                  (TipInt ** rightOp) <- infer e2 G
                                                  return (_ ** Ope (+) leftOp rightOp)
                                 _          => Nothing
  infer _ _               = Nothing


--- Type checking examples ---
partial
testOp : Maybe (t: Tip ** Expr Nil t)
testOp =  infer (lApp (lAnno (lLam (lLam (lInf (lOpe (Plus (lVar 1) (lVar 0)))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil
  
partial
testOpNeg : Maybe (t: Tip ** Expr Nil t)
testOpNeg =  infer (lApp (lAnno (lLam (lLam (lInf (lOpe (Plus (lVar 1) (lVar 0)))))) (TipFun TipBool (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil

partial
testVal : Maybe (t: Tip ** Expr Nil t)
testVal = infer (lVal 10) Nil

partial
testId : Maybe (t: Tip ** Expr Nil t)
testId = infer (lAnno (lLam (lInf (lVar 0))) (TipFun TipInt TipInt)) Nil

partial
testIdNeg : Maybe (t: Tip ** Expr Nil t)
testIdNeg = infer (lAnno (lLam (lInf (lVar 0))) TipInt) Nil

partial
testApp : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) TipInt))
testApp = check (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) Nil (TipFun (TipFun TipInt TipInt) TipInt)

partial
testAppNeg : Maybe (Expr Nil (TipFun TipInt TipInt))
testAppNeg = check (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) Nil (TipFun TipInt TipInt)

partial
testApp' : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt)))
testApp' = check (lLam (lLam (lInf (lApp (lVar 1) (lInf (lVar 0)))))) Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt))

partial
testApp'Neg : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipBool)))
testApp'Neg = check (lLam (lLam (lInf (lApp (lVar 1) (lInf (lVar 0)))))) Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipBool))

-- (App (lAnno (lLam (lInf (lOpe (Plus (lVar 0) (lVar 1))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 5)))
partial
testApp'' : Maybe (Expr Nil TipInt)
testApp'' = check (lInf (lApp (lAnno (lLam (lInf (lOpe (Plus (lVar 0) (lVal 4))))) (TipFun TipInt TipInt)) (lInf (lVal 4)))) Nil TipInt

partial
testApp''' : Maybe (Expr Nil TipInt)
testApp''' = check (lInf (lApp (lAnno (lLam (lInf (lOpe (Plus (lVar 0) (lApp (lAnno (lLam (lInf (lOpe (Plus (lVar 0) (lVar 1))))) (TipFun TipInt TipInt)) (lInf (lVal 5))))))) (TipFun TipInt TipInt)) (lInf (lVal 4)))) Nil TipInt

---------- Proofs ----------

TypeChk.exprTipEqSwapYescase = proof {
  intros;
  rewrite p;
  trivial;
}
