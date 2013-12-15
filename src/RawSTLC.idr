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

makeHasType : (i: Fin n) -> (G: Vect n Tip) -> (t: Tip ** HasType i G t)
makeHasType fZ     (t :: G) = (t ** stop)
makeHasType (fS k) (_ :: G) with (makeHasType k G)
  | (_ ** ht) = (_ ** pop ht)

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

isTipFun : {G: Vect n Tip} -> Expr G t -> Maybe (t': (Tip, Tip) ** Expr G (TipFun (fst t') (snd t')))
isTipFun {t=TipFun a b} e = Just ((a, b) ** e)
isTipFun                _ = Nothing

isTipProd : {G: Vect n Tip} -> Expr G t -> Maybe (t': (Tip, Tip) ** Expr G (TipProd (fst t') (snd t')))
isTipProd {t=TipProd a b} e = Just ((a, b) ** e)
isTipProd                 _ = Nothing

isTipSum : {G: Vect n Tip} -> Expr G t -> Maybe (t': (Tip, Tip) ** Expr G (TipSum (fst t') (snd t')))
isTipSum {t=TipSum a b} e = Just ((a, b) ** e)
isTipSum                _ = Nothing


mutual
  %assert_total
  check : CheckTerm -> (G: Vect n Tip) -> (t: Tip) -> Maybe (Expr G t)
  check (lInf iterm) G t             = do (t' ** e)  <- infer iterm G
                                          e'        <- exprTipEqSwap t' t G (decEq t' t) e
                                          return e' 
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
  check (lCase s l r) G t            = do (t' ** s')      <- infer s G
                                          ((a, b) ** s'') <- isTipSum s'
                                          l'              <- check l (a :: G) t
                                          r'              <- check r (b :: G) t
                                          return $ Case s'' l' r'
  check _ _ _                        = Nothing

  %assert_total
  infer : InfTerm -> (G: Vect n Tip) -> Maybe (t: Tip ** Expr G t)
  infer (lAnno cterm t) G     = do e <- check cterm G t
                                   return (_ ** e)
  infer (lApp f x) G          = do (t' ** f')      <- infer f G
                                   ((a, b) ** f'') <- isTipFun f'
                                   x'              <- check x G a
                                   return (_ ** App f'' x')
  infer lUnit G               = Just (_ ** U)
  infer (lVar n) G            = case natToFinFromVect n G of
                                  Just i => let (_ ** p) = makeHasType i G in
                                               Just (_ ** Var p)
                                  Nothing => Nothing
  infer (lVal i) G            = Just (_ ** Val i)
  infer (lBoo b) G            = Just (_ ** Boo b)
  infer (lFst p) G            = do (_ ** p') <- infer p G
                                   (_ ** p'') <- isTipProd p'
                                   return (_ ** Fst p'')
  infer (lSnd p) G            = do (_ ** p') <- infer p G
                                   (_ ** p'') <- isTipProd p'
                                   return (_ ** Snd p'')    
  infer (lFix f) G            = do (t' ** f') <- infer f G
                                   ((a, a) ** f'') <- isTipFun f'
                                   return (_ ** Fix f'')
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
testOp : Maybe (t: Tip ** Expr Nil t)
testOp =  infer (lApp (lAnno (lLam (lLam (lInf (lOpB (Plus (lInf (lVar 1)) (lInf (lVar 0))))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil
  
testOpNeg : Maybe (t: Tip ** Expr Nil t)
testOpNeg =  infer (lApp (lAnno (lLam (lLam (lInf (lOpB (Plus (lInf (lVar 1)) (lInf (lVar 0))))))) (TipFun TipBool (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil

testVal : Maybe (t: Tip ** Expr Nil t)
testVal = infer (lVal 10) Nil

testId : Maybe (t: Tip ** Expr Nil t)
testId = infer (lAnno (lLam (lInf (lVar 0))) (TipFun TipInt TipInt)) Nil

testIdNeg : Maybe (t: Tip ** Expr Nil t)
testIdNeg = infer (lAnno (lLam (lInf (lVar 0))) TipInt) Nil

testApp : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) TipInt))
testApp = check (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) Nil (TipFun (TipFun TipInt TipInt) TipInt)

testAppNeg : Maybe (Expr Nil (TipFun TipInt TipInt))
testAppNeg = check (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) Nil (TipFun TipInt TipInt)

testApp' : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt)))
testApp' = check (lLam (lLam (lInf (lApp (lVar 1) (lInf (lVar 0)))))) Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt))

testApp'Neg : Maybe (Expr Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipBool)))
testApp'Neg = check (lLam (lLam (lInf (lApp (lVar 1) (lInf (lVar 0)))))) Nil (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipBool))

testApp'' : Maybe (Expr Nil TipInt)
testApp'' = check (lInf (lApp (lAnno (lLam (lInf (lOpB (Plus (lInf (lVar 0)) (lInf (lVal 4)))))) (TipFun TipInt TipInt)) (lInf (lVal 4)))) Nil TipInt

eqTerm : CheckTerm
eqTerm = lLam (lLam (lInf (lOpB (Equal (lInf (lVar 1)) (lInf (lVar 0))))))

testEq : Maybe (Expr Nil (TipFun TipInt (TipFun TipInt TipBool)))
testEq = check eqTerm Nil (TipFun TipInt (TipFun TipInt TipBool))

testEqApp : Maybe (Expr Nil TipBool)
testEqApp = check (lInf (lApp (lApp (lAnno eqTerm (TipFun TipInt (TipFun TipInt TipBool))) (lInf (lVal 5))) (lInf (lVal 5)))) Nil TipBool

ifTerm : CheckTerm
ifTerm = lLam (lLam (lLam (lIf (lInf (lVar 2)) (lInf (lVar 1)) (lInf (lVar 0)))))

testIfTerm : Maybe (Expr Nil (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt))))
testIfTerm = check ifTerm Nil (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt)))

testIfApp : Maybe (Expr Nil TipInt) 
testIfApp = check (lInf (lApp (lApp (lApp (lAnno ifTerm (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt)))) (lInf (lBoo True))) (lInf (lVal 1))) (lInf (lVal 0)))) Nil TipInt

testIfApp' : Maybe (Expr Nil TipInt) 
testIfApp' = check (lInf (lApp (lApp (lApp (lAnno ifTerm (TipFun TipBool (TipFun TipInt (TipFun TipInt TipInt)))) (lInf (lOpB (Less (lInf (lVal 42)) (lInf (lVal 43)))))) (lInf (lVal 1))) (lInf (lVal 0)))) Nil TipInt

forever : InfTerm
forever = lFix (lAnno (lLam (lLam (lIf (lInf (lOpB (Equal (lInf (lVar 0)) (lInf (lVal 1)))))
                                       (lInf (lApp (lVar 1) (lInf (lVal 1))))
                                       (lInf (lVal 0))))) (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt)))

testFix : Maybe (t: Tip ** Expr Nil t)
testFix = infer forever Nil

---------- Proofs ----------

RawSTLC.exprTipEqSwapCase = proof
  intros
  rewrite p
  trivial

