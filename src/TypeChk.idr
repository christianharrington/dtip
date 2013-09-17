module TypeChk
import Interp

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
  
data TypeError : Type where
  typeError : String -> TypeError

lookupVar' : Nat -> Vect n Tip -> Maybe (HasType i G t)
lookupVar' Z     (t :: G') = Just stop
lookupVar' (S k) (_ :: G') = map pop (lookupVar' k G')
lookupVar' _     _         = Nothing

lookupVar : Nat -> Vect n Tip -> Maybe Tip
lookupVar n G = lookupVar' n (reverse G)

lookupVar'' : Nat -> Vect n Tip -> Maybe Tip
lookupVar'' n G = lookupVar'' n (reverse G)
  where lookupVar''' : Nat -> Vect n Tip -> Maybe Tip
        lookupVar''' Z     (t :: G') = Just t
        lookupVar''' (S k) (_ :: G') = lookupVar''' k G'
        lookupVar''' _     _         = Nothing

mutual
  check : CheckTerm -> Vect n Tip -> Tip -> Either TypeError Tip
  check (lInf iterm) G t            = infer iterm G
  check (lLam body) G (TipFun t t') = case check body (t :: G) t' of
                                           Right t''  => Right (TipFun t t'')
                                           Left err => Left err
  check _ _ _                       = Left $ typeError "Type error"

  infer : InfTerm -> Vect n Tip -> (t:Tip**Expr G t) --Either TypeError Tip
  infer (lAnno cterm t) G = check cterm G t
  infer (lApp f x) G      = case infer f G of
                                 Right (TipFun t t') => case check x G t of
                                                             Right t  => Right t'
                                                             Left err => Left err
                                 Left err            => Left err 
  infer (lVar n) G        = case lookupVar n G of
                                 Just t  => Right t
                                 Nothing => Left $ typeError "No such variable"
  infer (lVal i) G        = Right TipInt -- Only integers supported at the moment
  infer (lOpe op e1 e2) G = case op of
                                 '+' => case (infer e1 G, infer e2 G) of
                                             (Right TipInt, Right TipInt) => Right TipInt
                                             _                            => Left $ typeError "Incompatible operand type for +"
                                 _   => Left $ typeError "Unknown operator"



generateHasType : (i: Fin n) -> (G: Vect n Tip) -> HasType i G (index i G)
generateHasType fZ (t :: G)     = stop
generateHasType (fS k) (_ :: G) = pop (generateHasType k G)

mutual
  convertCheck : CheckTerm -> (n: Nat) -> (G: Vect n Tip) -> (t: Tip) -> Maybe (Expr G t)
  convertCheck (lInf iterm) i G t            = convertInf iterm i G t
  convertCheck (lLam body) i G (TipFun t t') = do b <- convertCheck body (S i) (t :: G) t'
                                                  return $ Lam b

  convertInf : InfTerm -> (n: Nat) -> (G: Vect n Tip) -> (t: Tip) -> Maybe (Expr G t)
  convertInf (lAnno cterm t) i G t' = convertCheck cterm i G t'
  convertInf (lApp f x) i G t'      = case infer f G of -- u' == t'
                                           Right (TipFun u u') => do g <- convertInf f i G (TipFun u t')
                                                                     y <- convertCheck x i G u
                                                                     return $ App g y
                                           Left _              => Nothing
  convertInf (lVar n) i G t         = case natToFin n i of
                                           Just f  => Just $ Var (generateHasType f G)
                                           Nothing => Nothing
  convertInf (lVal k) i G TipInt    = Just $ Val k
  convertInf (lOpe op e1 e2) G t = case op of
                                        '+' => do e1' <- convertInf e1 G TipInt
                                                  e2' <- convertInf e2 G TipInt
                                                  return $ Op (+) e1' e2'
                                        _   => Nothing 

--- Type checking examples ---
opTest : Either TypeError Tip
opTest = infer (lApp (lAnno (lLam (lLam (lInf (lOpe '+' (lVar 0) (lVar 1))))) (TipFun TipInt (TipFun TipInt TipInt))) (lInf (lVal 3))) Nil

appTest : Either TypeError Tip
appTest = infer (lAnno (lLam (lInf (lApp (lVar 0) (lInf (lVal 1))))) (TipFun (TipFun TipInt TipInt) TipInt)) Nil

appTest' : Either TypeError Tip
appTest' = infer (lAnno (lLam (lLam (lInf (lApp (lVar 0) (lInf (lVar 1)))))) (TipFun (TipFun TipInt TipInt) (TipFun TipInt TipInt))) Nil
