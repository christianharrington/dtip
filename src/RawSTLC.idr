module RawSTLC
import Interp

%default total

mutual
 data CheckTerm : Type where
   lInf  : InfTerm -> CheckTerm
   lLam  : CheckTerm -> CheckTerm
   lIf   : CheckTerm -> CheckTerm -> CheckTerm -> CheckTerm
   lPair : CheckTerm -> CheckTerm -> CheckTerm
   lInL  : CheckTerm -> CheckTerm
   lInR  : CheckTerm -> CheckTerm
   lCase : InfTerm -> CheckTerm -> CheckTerm -> CheckTerm
   
 data InfTerm : Type where
   lAnno : CheckTerm -> Tip -> InfTerm -- Annotate a checkable type with a type
   lApp  : InfTerm -> CheckTerm -> InfTerm
   lUnit : InfTerm
   lVar  : Nat -> InfTerm
   lVal  : Int -> InfTerm
   lBoo  : Bool -> InfTerm
   lFst  : InfTerm -> InfTerm
   lSnd  : InfTerm -> InfTerm
   lFix  : InfTerm -> InfTerm
   lOpU  : UnOp -> InfTerm
   lOpB  : BinOp -> InfTerm

 data BinOp : Type where
   Plus   : CheckTerm -> CheckTerm -> BinOp
   Minus  : CheckTerm -> CheckTerm -> BinOp
   Times  : CheckTerm -> CheckTerm -> BinOp
   Divide : CheckTerm -> CheckTerm -> BinOp
   Equal  : CheckTerm -> CheckTerm -> BinOp
   Less   : CheckTerm -> CheckTerm -> BinOp 

 data UnOp : Type where
   NNot : CheckTerm -> UnOp
  
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
exprTipEqSwap t t' G (Yes p) e = Just ?exprTipEqSwapCase
exprTipEqSwap t t' G (No  p) e = Nothing

mutual
  %assert_total
  check : CheckTerm -> (G: Vect n Tip) -> (t: Tip) -> Maybe (Expr G t)
  check (lInf iterm) G t             = do (t' ** e) <- infer iterm G
                                          expr <- exprTipEqSwap t' t G (decEq t' t) e -- Swap t with t'
                                          return expr
  check (lLam body) G (TipFun t t')  = do b <- check body (t :: G) t'
                                          return $ Lam b
  check (lIf c tb fb) G t            = do c'  <- check c G TipBool
                                          tb' <- check tb G t
                                          fb' <- check fb G t
                                          return $ If c' tb' fb'
  check (lPair a b) G (TipProd t t') = do a' <- check a G t
                                          b' <- check b G t'
                                          return $ Pair a' b'
  check (lInL e) G (TipSum t t')     = do e' <- check e G t
                                          return $ InL e' t' 
  check (lInR e) G (TipSum t t')     = do e' <- check e G t'
                                          return $ InR e' t
  check (lCase s l r) G t            = do (TipSum a b ** s') <- infer s G
                                          l'         <- check l (a :: G) t
                                          r'         <- check r (b :: G) t
                                          return $ Case s' l' r'
  check _ _ _                        = Nothing

  %assert_total
  infer : InfTerm -> (G: Vect n Tip) -> Maybe (t: Tip ** Expr G t)
  infer (lAnno cterm t) G     = do expr <- check cterm G t
                                   return (_ ** expr)
  infer (lApp f x) G          = do (TipFun t t' ** f') <- infer f G -- Should probably fail more gracefully
                                   x'                  <- check x G t
                                   return (_ ** App f' x')
  infer lUnit G               = Just (_ ** U)
  infer (lVar n) G            = do i        <- natToFinFromVect n G
                                   (_ ** p) <- makeHasType i G
                                   return (_ ** Var p) 
  infer (lVal i) G            = Just (_ ** Val i)
  infer (lBoo b) G            = Just (_ ** Boo b)
  infer (lFst p) G            = do (TipProd a b ** p') <- infer p G
                                   return (_ ** Fst p')
  infer (lSnd p) G            = do (TipProd a b ** p') <- infer p G
                                   return (_ ** Snd p')
  infer (lFix f) G            = do (TipFun t t ** f') <- infer f G
                                   return (_ ** Fix f')
  infer (lOpU (NNot a)) G     = do a' <- check a G TipBool
                                   return (_ ** OpU Nay a')
  infer (lOpB (Plus a b)) G   = do leftOp  <- check a G TipInt
                                   rightOp <- check b G TipInt
                                   return (_ ** OpB Add leftOp rightOp)
  infer (lOpB (Minus a b)) G  = do leftOp  <- check a G TipInt
                                   rightOp <- check b G TipInt
                                   return (_ ** OpB Sub leftOp rightOp)
  infer (lOpB (Times a b)) G  = do leftOp  <- check a G TipInt
                                   rightOp <- check b G TipInt
                                   return (_ ** OpB Mul leftOp rightOp)
  infer (lOpB (Divide a b)) G = do leftOp  <- check a G TipInt
                                   rightOp <- check b G TipInt
                                   return (_ ** OpB Div leftOp rightOp)
  infer (lOpB (Equal a b)) G  = do leftOp  <- check a G TipInt
                                   rightOp <- check b G TipInt
                                   return (_ ** OpB Eql leftOp rightOp)
  infer (lOpB (Less a b)) G   = do leftOp  <- check a G TipInt
                                   rightOp <- check b G TipInt
                                   return (_ ** OpB Lt leftOp rightOp)
  infer _ _                   = Nothing


--- Type checking examples ---
partial
testOp : Maybe (t: Tip ** Expr Nil t)
testOp =  infer (lApp (lAnno (lLam (lLam (lInf (lOpB (Plus (lInf (lVar 1)) (lInf (lVar 0))))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil
  
partial
testOpNeg : Maybe (t: Tip ** Expr Nil t)
testOpNeg =  infer (lApp (lAnno (lLam (lLam (lInf (lOpB (Plus (lInf (lVar 1)) (lInf (lVar 0))))))) (TipFun TipBool (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil

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
testApp'' = check (lInf (lApp (lAnno (lLam (lInf (lOpB (Plus (lInf (lVar 0)) (lInf (lVal 4)))))) (TipFun TipInt TipInt)) (lInf (lVal 4)))) Nil TipInt

--partial
--testApp''' : Maybe (Expr Nil TipInt)
--testApp''' = check (lInf (lApp (lAnno (lLam (lOpB (Plus (lInf (lVar 0)) (lInf (lApp (lAnno (lLam (lOpB (Plus (lInf (lVar 0)) (lInf (lVar 1)))))) (TipFun TipInt TipInt)) (lInf (lVal 5)))))))) (TipFun TipInt TipInt)) (lInf (lVal 4)))) Nil TipInt

eqTerm : CheckTerm --Expr Nil (TipFun TipInt (TipFun TipInt TipBool))
eqTerm = lLam (lLam (lInf (lOpB (Equal (lInf (lVar 1)) (lInf (lVar 0))))))

partial
testEq : Maybe (Expr Nil (TipFun TipInt (TipFun TipInt TipBool)))
testEq = check eqTerm Nil (TipFun TipInt (TipFun TipInt TipBool))

partial
testEqApp : Maybe (Expr Nil TipBool)
testEqApp = check (lInf (lApp (lApp (lAnno eqTerm (TipFun TipInt (TipFun TipInt TipBool))) (lInf (lVal 5))) (lInf (lVal 5)))) Nil TipBool

ifTerm : CheckTerm
ifTerm = lLam (lLam (lLam (lIf (lInf (lVar 2)) (lInf (lVar 1)) (lInf (lVar 0)))))

partial
testIfTerm : Maybe (Expr Nil (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt))))
testIfTerm = check ifTerm Nil (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt)))

partial -- lOpB (Less (lInf (lVal 42)) (lInf (lVal 43))))
testIfApp : Maybe (Expr Nil TipInt) 
testIfApp = check (lInf (lApp (lApp (lApp (lAnno ifTerm (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt)))) (lInf (lBoo True))) (lInf (lVal 1))) (lInf (lVal 0)))) Nil TipInt

partial -- lOpB (Less (lInf (lVal 42)) (lInf (lVal 43))))
testIfApp' : Maybe (Expr Nil TipInt) 
testIfApp' = check (lInf (lApp (lApp (lApp (lAnno ifTerm (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt)))) (lInf (lOpB (Less (lInf (lVal 42)) (lInf (lVal 43)))))) (lInf (lVal 1))) (lInf (lVal 0)))) Nil TipInt


---------- Proofs ----------

RawSTLC.exprTipEqSwapCase = proof
  intros
  rewrite p
  trivial

