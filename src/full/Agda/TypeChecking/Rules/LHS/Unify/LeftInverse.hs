{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

{-| Functions for building the left inverse part of a 'UnifyEquiv'.
 -}

module Agda.TypeChecking.Rules.LHS.Unify.LeftInverse where

import Prelude hiding ((!!), null)

import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Data.List (zip4, zipWith4)
import Data.Functor
import qualified Agda.Syntax.Concrete.Name as C

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Monad (freshAbstractQName)

import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile (compileClauses)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalTerm)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records

import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Unify.Types

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size

import Agda.Utils.Impossible


data DigestedUnifyStep
  = DSolution Int (Dom Type) (FlexibleVar Int) Term (Either () ())
  | DInjectivity Int Type QName Args Args ConHead
  | DEtaExpandVar (FlexibleVar Int) QName Args

instance PrettyTCM DigestedUnifyStep where
  prettyTCM (DSolution a b c d e) = prettyTCM (Solution a b c d e)
  prettyTCM (DInjectivity a b c d e f) = prettyTCM (Injectivity a b c d e f)
  prettyTCM (DEtaExpandVar a b c) = prettyTCM (EtaExpandVar a b c)

data DigestedUnifyLogEntry
  = DUnificationStep UnifyState DigestedUnifyStep UnifyOutput

type DigestedUnifyLog = [(DigestedUnifyLogEntry,UnifyState)]

-- | Pre-process a UnifyLog so that we catch unsupported steps early.
digestUnifyLog :: UnifyLog -> Either NoLeftInv DigestedUnifyLog
digestUnifyLog log = forM log \(UnificationStep s step out, s') -> do
  let illegal     = Left $ Illegal step
      unsupported = Left $ UnsupportedYet step
      ret step    = pure (DUnificationStep s step out, s')
  case step of
    Solution a b c d e   -> ret $ DSolution a b c d e
    Injectivity a b c d e f -> ret $ DInjectivity a b c d e f
    EtaExpandVar a b c   -> ret $ DEtaExpandVar a b c
    Deletion{}           -> illegal
    TypeConInjectivity{} -> illegal
    -- These should end up in a NoUnify
    Conflict{}    -> __IMPOSSIBLE__
    LitConflict{} -> __IMPOSSIBLE__
    Cycle{}       -> __IMPOSSIBLE__
    _             -> unsupported

instance PrettyTCM NoLeftInv where
  prettyTCM (UnsupportedYet s) = fsep $ pwords "It relies on" ++ [explainStep s <> ","] ++ pwords "which is not yet supported"
  prettyTCM UnsupportedCxt     = fwords "it relies on higher-dimensional unification, which is not yet supported"
  prettyTCM (Illegal s)        = fsep $ pwords "It relies on" ++ [explainStep s <> ","] ++ pwords "which is incompatible with" ++ [text "Cubical Agda"]
  prettyTCM NoCubical          = fwords "Cubical Agda is disabled"
  prettyTCM WithKEnabled       = fwords "The K rule is enabled"
  prettyTCM SplitOnStrict      = fwords "It splits on a type in SSet"
  prettyTCM SplitOnFlat        = fwords "It splits on a @♭ argument"
  prettyTCM (CantTransport t)  = fsep $ pwords "The type" <> [prettyTCM t] <> pwords "can not be transported"
  prettyTCM (CantTransport' t) = fsep $ pwords "The type" <> [prettyTCM t] <> pwords "can not be transported"

data NoLeftInv
  = UnsupportedYet {badStep :: UnifyStep}
  | Illegal        {badStep :: UnifyStep}
  | NoCubical
  | WithKEnabled
  | SplitOnStrict  -- ^ splitting on a Strict Set.
  | SplitOnFlat    -- ^ splitting on a @♭ argument
  | UnsupportedCxt
  | CantTransport  (Closure (Abs Type))
  | CantTransport' (Closure Type)
  deriving Show

-- | Build the left inverse part of a 'UnifyEquiv' (@τ@, @leftInv@).
buildLeftInverse :: UnifyState -> UnifyLog -> TCM (Either NoLeftInv (Substitution, Substitution))
buildLeftInverse s0 log = Bench.billTo [Bench.UnifyIndices, Bench.CubicalLeftInversion] $ case digestUnifyLog log of
  Left no -> do
    reportSDoc "tc.lhs.unify.inv.badstep" 20 $ "No Left Inverse:" <+> prettyTCM (badStep no)
    return (Left no)
  Right log -> do

    reportSDoc "tc.lhs.unify.inv.badstep" 20 $ do
      cubical <- cubicalOption
      "cubical:" <+> text (show cubical)
    reportSDoc "tc.lhs.unify.inv.badstep" 20 $ do
      pathp <- getTerm' builtinPathP
      "pathp:" <+> text (show $ isJust pathp)
    let
      cond = andM
        -- TODO: handle open contexts: they happen during "higher dimensional" unification,
        --       in injectivity cases.
        [ null <$> getContext
        ]

      compose :: [(Retract, Term)] -> ExceptT NoLeftInv TCM Retract
      compose [] = __IMPOSSIBLE__
      compose [(xs, _)] = pure xs
      compose ((x, t):xs) = do
        r <- compose xs
        ExceptT $ composeRetract x t r <&> \case
          Left e  -> Left (CantTransport e)
          Right x -> Right x

    ifNotM cond (return $ Left UnsupportedCxt) $ do
    equivs <- forM log $ uncurry buildEquiv
    case sequence equivs of
      Left no -> do
        reportSDoc "tc.lhs.unify.inv.badstep" 20 $ "No Left Inverse:" <+> prettyTCM (badStep no)
        return (Left no)
      Right xs -> runExceptT (compose xs) >>= \case
        Left no -> return (Left no)
        Right (_, _, tau0, leftInv0) -> do
        -- Γ,φ,us =_Δ vs ⊢ τ0 : Γ', φ
        -- leftInv0 : [wkS |φ,us =_Δ vs| ρ,1,refls][τ] = idS : Γ,φ,us =_Δ vs
        let tau = tau0 `composeS` raiseS 1
        unview <- intervalUnview'
        let replaceAt n x xs = xs0 ++ x:xs1
                    where (xs0,_:xs1) = splitAt n xs
        let max r s = unview $ IMax (argN r) (argN s)
            neg r = unview $ INeg (argN r)
        let phieq = neg (var 0) `max` var (size (eqTel s0) + 1)
                          -- I + us =_Δ vs -- inplaceS
        let leftInv = termsS __IMPOSSIBLE__ $ replaceAt (size (varTel s0)) phieq $ map (lookupS leftInv0) $ downFrom (size (varTel s0) + 1 + size (eqTel s0))
        let working_tel = abstract (varTel s0) (ExtendTel __DUMMY_DOM__ $ Abs "phi0" $ (eqTel s0))
        reportSDoc "tc.lhs.unify.inv" 20 $ "=== before mod"
        do
            addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau0    :" <+> prettyTCM tau0
            addContext working_tel $ addContext ("r" :: String, __DUMMY_DOM__)
                                  $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv0:  " <+> prettyTCM leftInv0

        reportSDoc "tc.lhs.unify.inv" 20 $ "=== after mod"
        do
            addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau    :" <+> prettyTCM tau
            addContext working_tel $ addContext ("r" :: String, __DUMMY_DOM__)
                                  $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv:   " <+> prettyTCM leftInv

        return $ Right (tau,leftInv)

type Retract = (Telescope, Substitution, Substitution, Substitution)
     -- Γ (the problem, including equalities),
     -- Δ ⊢ ρ : Γ
     -- Γ ⊢ τ : Δ
     -- Γ, i : I ⊢ leftInv : Γ, such that (λi. leftInv) : ρ[τ] = id_Γ

--- Γ ⊢ us : Δ   Γ ⊢ termsS e us : Δ
termsS ::  DeBruijn a => Impossible -> [a] -> Substitution' a
termsS e xs = reverse xs ++# EmptyS e

composeRetract :: Retract -> Term -> Retract -> TCM (Either (Closure (Abs Type)) Retract)
composeRetract (prob0,rho0,tau0,leftInv0) phi0 (prob1,rho1,tau1,leftInv1) = do
  reportSDoc "tc.lhs.unify.inv" 20 $ "=== composing"
  reportSDoc "tc.lhs.unify.inv" 20 $ "Γ0   :" <+> prettyTCM prob0
  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau0  :" <+> prettyTCM tau0
  reportSDoc "tc.lhs.unify.inv" 20 $ "Γ1   :" <+> prettyTCM prob1
  addContext prob1 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau1  :" <+> prettyTCM tau1


  {-
  Γ0 = prob0
  S0 ⊢ ρ0 : Γ0
  Γ0 ⊢ τ0 : S0
  Γ0 ⊢ leftInv0 : ρ0[τ0] = idΓ0
  Γ0 ⊢ φ0
  Γ0,φ0 ⊢ leftInv0 = refl

  Γ1 = prob1
  S1 ⊢ ρ1 : Γ1
  Γ1 ⊢ τ1 : S1
  Γ1 ⊢ leftInv1 : ρ1[τ1] = idΓ1
  Γ1 ⊢ φ1 = φ0[τ0] (**)
  Γ1,φ1 ⊢ leftInv1 = refl
  S0 = Γ1

  (**) implies?
  Γ0,φ0 ⊢ leftInv1[τ0] = refl  (*)


  S1 ⊢ ρ := ρ0[ρ1] : Γ0
  Γ0 ⊢ τ := τ1[τ0] : S1
  -}

  let prob = prob0
  let rho = rho1 `composeS` rho0
  let tau = tau0 `composeS` tau1

  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau  :" <+> prettyTCM tau

  {-
  Γ0 ⊢ leftInv : ρ[τ] = idΓ0
  Γ0 ⊢ leftInv : ρ0[ρ1[τ1]][τ0] = idΓ0
  Γ0 ⊢ step0 := ρ0[leftInv1[τ0]] : ρ0[ρ1[τ1]][τ0] = ρ0[τ0]

  Γ0,φ0 ⊢ step0 = refl     by (*)


  Γ0 ⊢ leftInv := step0 · leftInv0 : ρ0[ρ1[τ1]][τ0] = idΓ0

  Γ0 ⊢ leftInv := tr (\ i → ρ0[ρ1[τ1]][τ0] = leftInv0[i]) φ0 step0
  Γ0,φ0 ⊢ leftInv = refl  -- because it will become step0, which is refl when φ0

  Γ0, i : I ⊢ hcomp {Γ0} (\ j → \ { (i = 0) -> ρ0[ρ1[τ1]][τ0]
                                  ; (i = 1) -> leftInv0[j]
                                  ; (φ0 = 1) -> γ0
                                  })
                         (step0[i])




  -}
  let step0 = liftS 1 tau0 `composeS` leftInv1 `composeS` rho0

  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv0  :" <+> prettyTCM leftInv0
  addContext prob1 $ reportSDoc "tc.lhs.unify.inv" 20 $ "rho0  :" <+> prettyTCM rho0
  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau0  :" <+> prettyTCM tau0
  addContext prob0 $ reportSDoc "tc.lhs.unify.inv" 20 $ "rhos0[tau0]  :" <+> prettyTCM (tau0 `composeS` rho0)

  addContext prob1 $ addContext ("r" :: String, __DUMMY_DOM__) $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv1  :" <+> prettyTCM leftInv1
  addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) $ reportSDoc "tc.lhs.unify.inv" 20 $ "step0  :" <+> prettyTCM step0

  interval <- primIntervalType
  max <- primIMax
  neg <- primINeg
  result <- sequenceA <$> do
    addContext prob0 $ runNamesT (teleNames prob0) $ do
             phi <- open phi0
             g0 <- open $ raise (size prob0) prob0
             step0 <- open $ Abs "i" $ step0 `applySubst` teleArgs prob0
             leftInv0 <- open $ Abs "i" $ map unArg $ leftInv0 `applySubst` teleArgs prob0
             bind "i" $ \ i -> addContext ("i" :: String, defaultDom interval) $ do
              tel <- bind "_" $ \ (_ :: NamesT tcm Term) -> g0
              step0i <- lazyAbsApp <$> step0 <*> i
              face <- pure max <@> (pure neg <@> i) <@> phi
              leftInv0 <- leftInv0
              i <- i
              -- this composition could be optimized further whenever step0i is actually constant in i.
              lift $ runExceptT (map unArg <$> transpSysTel' True tel [(i, leftInv0)] face step0i)
  case result of
    Left  cl      -> pure (Left cl)
    Right leftInv -> do
      let sigma = termsS __IMPOSSIBLE__ $ absBody leftInv
      verboseS "tc.lhs.unify.inv" 20 do
        addContext prob0 $ addContext ("r" :: String, __DUMMY_DOM__) do
          reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv    :" <+> prettyTCM (absBody leftInv)
          reportSDoc "tc.lhs.unify.inv" 40 $ "leftInv    :" <+> pretty (absBody leftInv)
          reportSDoc "tc.lhs.unify.inv" 40 $ "leftInvSub :" <+> pretty sigma
      return $ Right (prob, rho, tau, sigma)

conTermArgs :: ConHead -> Term -> Maybe Args
conTermArgs ch = \case
  Con ch' _ es | conName ch' == conName ch -> allApplyElims es
  _                                        -> Nothing

freshInjectivityQName :: String -> TCM QName
freshInjectivityQName = freshAbstractQName noFixity' . C.setNotInScope . C.simpleName

isNonDependentTelescope :: Telescope -> Bool
isNonDependentTelescope tel = and $ zipWith noDep [0 ..] $ map (snd . unDom) $ telToList tel
  where
    noDep i t = not $ any (`freeIn` t) [0 .. i - 1]

injectivityVisibleFieldPositions :: Telescope -> Maybe [Int]
injectivityVisibleFieldPositions tel = do
  let entries = telToList tel
      hiddenPrefix = length $ takeWhile ((== Hidden) . getHiding) entries
      visibleSuffix = drop hiddenPrefix entries
  Control.Monad.guard $ all ((/= Hidden) . getHiding) visibleSuffix
  pure [ hiddenPrefix .. length entries - 1 ]

supportsIndexedFieldInjectivity :: Telescope -> Bool
supportsIndexedFieldInjectivity tel = case injectivityVisibleFieldPositions tel of
  Nothing -> False
  Just positions ->
    and [ not $ any (`freeIn` ty) earlierVisible
        | (i, dom) <- zip [0 ..] (telToList tel)
        , let ty = snd $ unDom dom
        , i `elem` positions
        , let earlierVisible = map (\ p -> i - 1 - p) $ filter (< i) positions
        ]

defineInjectivityProjections
  :: Telescope
  -> Type
  -> ConHead
  -> Telescope
  -> TCM ([QName], [Dom Type])
defineInjectivityProjections prefixTel a con ctel = do
  names <- forM [0 .. size ctel - 1] $ \ i ->
    freshInjectivityQName $ "inj-proj-" ++ show i
  let
    fieldTypes = ([ Def f [] `apply` [argN $ var 0] | f <- reverse names ] ++# raiseS 1) `applySubst`
      flattenTel ctel
    projTel = abstract prefixTel $ ExtendTel (defaultDom a) $ Abs "d" EmptyTel

  forM_ (zip3 (downFrom $ size fieldTypes) names fieldTypes) $ \ (i, projName, ty) -> do
    let
      projType = abstract projTel <$> ty
      cpi    = ConPatternInfo defaultPatternInfo False False (Just $ argN $ raise (size ctel) a) False
      conp   = defaultNamedArg $ ConP con cpi $ teleNamedArgs ctel
      sigma  = Con con ConOSystem (map Apply $ teleArgs ctel) `consS` raiseS (size ctel)
      clause = empty
        { clauseTel         = abstract prefixTel ctel
        , namedClausePats   = [ conp ]
        , clauseBody        = Just $ var i
        , clauseType        = Just $ argN $ applySubst sigma $ unDom ty
        , clauseRecursive   = NotRecursive
        , clauseUnreachable = Just False
        }
    noMutualBlock $ do
      (mst, _, cc) <- compileClauses Nothing [clause]
      fun <- emptyFunctionData <&> \ fun -> fun
        { _funClauses    = [clause]
        , _funCompiled   = Just cc
        , _funSplitTree  = mst
        , _funProjection = Left MaybeProjection
        , _funMutual     = Just []
        , _funTerminates = Just True
        }
      lang <- getLanguage
      inTopContext $ addConstant projName $
        (defaultDefn defaultArgInfo projName (unDom projType) lang $ FunctionDefn fun)
          { defNoCompilation = True
          }

  pure (names, fieldTypes)
-- | Build the left inverse corresponding to a single unification step.
buildEquiv :: DigestedUnifyLogEntry -> UnifyState -> TCM (Either NoLeftInv (Retract,Term))
buildEquiv (DUnificationStep st step@(DSolution k ty fx tm side) output) next = runExceptT $ do
        let
          cantTransport' :: ExceptT (Closure Type) TCM b -> ExceptT NoLeftInv TCM b
          cantTransport' m = withExceptT CantTransport' m
          cantTransport :: ExceptT (Closure (Abs Type)) TCM b -> ExceptT NoLeftInv TCM b
          cantTransport m = withExceptT CantTransport m

        reportSDoc "tc.lhs.unify.inv" 20 $ "step unifyState:" <+> prettyTCM st
        reportSDoc "tc.lhs.unify.inv" 20 $ "step step:" <+> addContext (varTel st) (prettyTCM step)
        unview <- intervalUnview'
        cxt <- getContextTelescope
        reportSDoc "tc.lhs.unify.inv" 20 $ "context:" <+> prettyTCM cxt
        let
          m = varCount st
          gamma = varTel st
          eqs = eqTel st
          -- k counts in eqs from the left
          u = eqLHS st !! k
          v = eqRHS st !! k
          -- Γ ⊢ perm : Γ' is a reordering used by instantiateTelescope to ensure the
          -- resulting context is well-formed. Works on de Bruijn levels.
          perm = fromMaybe __IMPOSSIBLE__ $ unifySolutionPerm output
          -- The new de Bruijn index of fx in Γ'. The target context for τ is obtained by dropping
          -- x from Γ' (and the kth equation from the equation telescope) and instantiating
          -- it with u (resp. refl).
          x = fromMaybe __IMPOSSIBLE__ $ lookupRP (reverseP perm) (flexVar fx)
          neqs = size eqs
          phis = 1
        interval <- lift $ primIntervalType
         -- Γ, φ : I
        let gamma_phis = abstract gamma $ telFromList $
              map (defaultDom . (,interval) . ("phi" ++) . show) [0 .. phis - 1]
        -- working_tel = Γ, φ : I, eqs : lhs ≡ rhs
        working_tel <- abstract gamma_phis <$>
          cantTransport' (pathTelescope' (raise phis $ eqTel st) (raise phis $ eqLHS st) (raise phis $ eqRHS st))
        -- working_tel' = Γ'           , φ : I, eqs : lhs ≡ rhs
        --              = Γ₁, x : A, Γ₂, φ : I, eqs : lhs ≡ rhs
        let permw = liftP (size working_tel - size gamma) perm
        working_tel' <- pure $ permuteTel permw working_tel
        reportSDoc "tc.lhs.unify.inv" 20 $ vcat
          [ "working tel:" <+> prettyTCM (working_tel :: Telescope)
          , addContext working_tel $ "working tel args:" <+> prettyTCM (teleArgs working_tel :: [Arg Term])
          , "perm:" <+> prettyTCM perm
          ]
        (tau,leftInv,phi) <- addContext working_tel $ runNamesT [] $ do
          let
            raiseFrom :: Subst a => Telescope -> a -> a
            raiseFrom tel x = raise (size working_tel - size tel) x
            bindSplit (tel1,tel2) = (tel1,AbsN (teleNames tel1) tel2)
          u <- open . raiseFrom gamma . unArg $ u
          v <- open . raiseFrom gamma . unArg $ v
          -- φ
          let phi = raiseFrom gamma_phis $ var 0
          -- working_tel ⊢ γ₁,x,γ₂,φ,eqs : working_tel'
          let all_args = permute permw $ teleArgs working_tel

          -- . ⊢ Γ₁  ,  γ₁. x : A, Γ₂, φ : I, eqs : lhs ≡ rhs
          let (gamma1, xxi) = bindSplit $ splitTelescopeAt (size gamma - x - 1) working_tel'
              (gamma1_args,xxi_args) = splitAt (size gamma1) all_args
              (_x_arg:xi_args) = xxi_args
              (x_arg:xi0,k_arg:xi1) = splitAt (size gamma - size gamma1 + phis + k) xxi_args
              -- working_tel ⊢ x : A, Γ₂, φ : I, eqs : lhs ≡ rhs
              xxi_here = absAppN xxi $ map unArg gamma1_args
              --                                                  x:A, Γ₂               φ
              (xpre,krest) = bindSplit $ splitTelescopeAt ((size gamma - size gamma1) + phis + k) xxi_here
          k_arg <- open $ unArg k_arg
          xpre <- open xpre
          krest <- open krest
          -- Δ₀ = Γ₁, Γ₂
          -- Δ  = x eq. Δ₀, φ : I, eqs-k : lhs-k ≡ rhs-k
          delta <- bindN ["x","eq"] $ \ [x,eq] -> do
                     let pre = apply1 <$> xpre <*> x
                     abstractN pre $ \ args ->
                       apply1 <$> applyN krest (x:args) <*> eq
          -- working_tel ⊢ delta0_args : Δ₀
          let delta0_args = xi0 ++ xi1
          let appSide = case side of
                          Left{} -> id
                          Right{} -> unview . INeg . argN
          let
                  -- csingl :: NamesT tcm Term -> NamesT tcm [Arg Term]
                  csingl i = mapM (fmap defaultArg) $ csingl' i
                  -- csingl' :: NamesT tcm Term -> [NamesT tcm Term]
                  csingl' i = [ k_arg <@@> (u, v, appSide <$> i)
                              , lam "j" $ \ j ->
                                  let r i j = case side of
                                            Left{} -> unview (IMax (argN j) (argN i))
                                            Right{} -> unview (IMin (argN j) (argN . unview $ INeg $ argN i))
                                  in k_arg <@@> (u, v, r <$> i <*> j)
                              ]
          let replaceAt n x xs = xs0 ++ x:xs1
                where (xs0,_:xs1) = splitAt n xs
              dropAt n xs = xs0 ++ xs1
                where (xs0,_:xs1) = splitAt n xs
          delta <- open delta
          -- d = i. Δ (k i) (λ j → k (i ∧ j))
          d <- bind "i" $ \ i -> applyN delta (csingl' i)

          -- Andrea 06/06/2018
          -- We do not actually add a transp/fill if the family is
          -- constant (TODO: postpone for metas) This is so variables
          -- whose types do not depend on "x" are left alone, in
          -- particular those the solution "t" depends on.
          --
          -- We might want to instead use the info discovered by instantiateTelescope
          -- when checking if "t" depends on "x" to decide what
          -- to transp and what not to.
          let flag = True
          tau <- (gamma1_args ++) <$> lift (cantTransport (transpTel' flag d phi delta0_args))
          reportSDoc "tc.lhs.unify.inv" 20 $ "tau    :" <+> prettyTCM (map (setHiding NotHidden) tau)
          leftInv <- do
            gamma1_args <- open gamma1_args
            phi <- open phi
            -- xxi_here <- open xxi_here
            -- (xi_here_f :: Abs Telescope) <- bind "i" $ \ i -> apply <$> xxi_here <*> (take 1 `fmap` csingl i)
            -- xi_here_f <- open xi_here_f
            -- xi_args <- open xi_args
            -- xif <- bind "i" $ \ i -> do
            --                      m <- (runExceptT <$> (trFillTel' flag <$> xi_here_f <*> phi <*> xi_args <*> i))
            --                      either __IMPOSSIBLE__ id <$> lift m
            -- xif <- open xif

            xi0 <- open xi0
            xi1 <- open xi1
            delta0 <- bind "i" $ \ i -> apply <$> xpre <*> (take 1 `fmap` csingl i)
            delta0 <- open delta0
            xi0f <- bind "i" $ \ i -> do
                                 m <- trFillTel' flag <$> delta0 <*> phi <*> xi0 <*> i
                                 lift (cantTransport m)
            xi0f <- open xi0f

            delta1 <- bind "i" $ \ i -> do

                   args <- mapM (open . unArg) =<< (lazyAbsApp <$> xi0f <*> i)
                   apply <$> applyN krest (take 1 (csingl' i) ++ args) <*> (drop 1 `fmap` csingl i)
            delta1 <- open delta1
            xi1f <- bind "i" $ \ i -> do
                                 m <- trFillTel' flag <$> delta1 <*> phi <*> xi1 <*> i
                                 lift (cantTransport m)
            xi1f <- open xi1f
            fmap absBody $ bind "i" $ \ i' -> do
              let (+++) m = liftM2 (++) m
                  i = cl (lift primINeg) <@> i'
              fmap (permute (invertP __IMPOSSIBLE__ permw)) $
                gamma1_args +++ (take 1 `fmap` csingl i +++ ((lazyAbsApp <$> xi0f <*> i) +++ (drop 1 `fmap` csingl i +++ (lazyAbsApp <$> xi1f <*> i))))
          return (tau,leftInv,phi)
        iz <- lift $ primIZero
        io <- lift $ primIOne
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tau    :" <+> prettyTCM (map (setHiding NotHidden) tau)
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "tauS   :" <+> prettyTCM (termsS __IMPOSSIBLE__ $ map unArg tau)
        addContext working_tel $ addContext ("r" :: String, defaultDom interval)
                               $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv:   " <+> prettyTCM (map (setHiding NotHidden) leftInv)
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv[0]:" <+> (prettyTCM =<< reduce (subst 0 iz $ map (setHiding NotHidden) leftInv))
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "leftInv[1]:" <+> (prettyTCM =<< reduce  (subst 0 io $ map (setHiding NotHidden) leftInv))
        addContext working_tel $ reportSDoc "tc.lhs.unify.inv" 20 $ "[rho]tau :" <+>
          prettyTCM (applySubst (termsS __IMPOSSIBLE__ $ map unArg tau) $ fromPatternSubstitution
                                                                      $ raise (size (eqTel st) - 1 + phis)
                                                                      $ unifySubst output)
        reportSDoc "tc.lhs.unify.inv" 20 $ "."
        let rho0 = fromPatternSubstitution $ unifySubst output
        addContext (varTel next) $ addContext (eqTel next) $ reportSDoc "tc.lhs.unify.inv" 20 $
          "prf :" <+> prettyTCM (fromPatternSubstitution $ unifyProof output)
        let c0 = Lam defaultArgInfo $ Abs "i" $ raise 1 $ lookupS (fromPatternSubstitution $ unifyProof output) (neqs - k - 1)
        let c = liftS (size $ eqTel next) (raiseS 1) `applySubst` c0
        addContext (varTel next) $ addContext ("φ" :: String, __DUMMY_DOM__) $ addContext (raise 1 $ eqTel next) $
          reportSDoc "tc.lhs.unify.inv" 20 $ "c :" <+> prettyTCM c
        let rho = singletonS (neqs - k - 1) c  `composeS` liftS (1 + neqs) rho0
        reportSDoc "tc.lhs.unify.inv" 20 $ text "old_sizes: " <+> pretty (size $ varTel st, size $ eqTel st)
        reportSDoc "tc.lhs.unify.inv" 20 $ text "new_sizes: " <+> pretty (size $ varTel next, size $ eqTel next)
        addContext (varTel next) $ addContext ("φ" :: String, __DUMMY_DOM__) $ addContext (raise 1 $ eqTel next) $
          reportSDoc "tc.lhs.unify.inv" 20 $ "rho   :" <+> prettyTCM rho
        return $ ((working_tel
                 , rho
                 , termsS __IMPOSSIBLE__ $ map unArg tau
                 , termsS __IMPOSSIBLE__ $ map unArg leftInv)
                 , phi)
buildEquiv (DUnificationStep st step@(DInjectivity k a d pars ixs ch) _output) next = runExceptT $ do
        let
          rawStep = Injectivity k a d pars ixs ch
          unsupported :: ExceptT NoLeftInv TCM b
          unsupported = throwError $ UnsupportedYet rawStep
          unsupportedBecause :: String -> ExceptT NoLeftInv TCM b
          unsupportedBecause _ = unsupported
          cantTransport' :: ExceptT (Closure Type) TCM b -> ExceptT NoLeftInv TCM b
          cantTransport' m = withExceptT CantTransport' m
          cantTransport :: ExceptT (Closure (Abs Type)) TCM b -> ExceptT NoLeftInv TCM b
          cantTransport m = withExceptT CantTransport m

        reportSDoc "tc.lhs.unify.inv" 20 $ "buildEquiv Injectivity"
        reportSDoc "tc.lhs.unify.inv" 20 $ "step unifyState:" <+> prettyTCM st
        reportSDoc "tc.lhs.unify.inv" 20 $ "step step:" <+> addContext (varTel st) (prettyTCM step)

        Datatype{ dataIxs = nixs } <- theDef <$> (lift $ getConstInfo d)

        let
          gamma = varTel st
          eqs   = eqTel st
          u0    = eqLHS st !! k
          v0    = eqRHS st !! k
          neqs  = size eqs
          phis  = 1
          (eqListTel1, _ : _eqListTel2) = splitAt k $ telToList eqs
          eqTel1 = telFromList eqListTel1
          prefixTel = gamma `abstract` eqTel1

        cdef <- lift $ getConInfo ch
        let ctype = defType cdef `piApply` pars
        TelV ctel _ <- lift $ addContext prefixTel $ telView ctype

        uArgs0 <- maybe (unsupportedBecause "lhs constructor args") pure $ conTermArgs ch (unArg u0)
        vArgs0 <- maybe (unsupportedBecause "rhs constructor args") pure $ conTermArgs ch (unArg v0)
        Control.Monad.unless (length uArgs0 == size ctel) __IMPOSSIBLE__
        Control.Monad.unless (length vArgs0 == size ctel) __IMPOSSIBLE__

        let
          indexedWithFields = nixs /= 0 && size ctel /= 0
          componentPositions
            | indexedWithFields = fromMaybe [] $ injectivityVisibleFieldPositions ctel
            | otherwise         = [0 .. size ctel - 1]
          componentOffset = case componentPositions of
            []    -> size ctel
            i : _ -> i
          componentCount = length componentPositions
          hiddenPrefixCount = componentOffset
          hiddenPrefixArgs0 = take hiddenPrefixCount uArgs0
          hiddenPrefixVArgs0 = take hiddenPrefixCount vArgs0
          componentUArgs0 = drop hiddenPrefixCount uArgs0
          componentVArgs0 = drop hiddenPrefixCount vArgs0
          fieldArgInfo = map getArgInfo uArgs0
          componentArgInfo = drop hiddenPrefixCount fieldArgInfo

        Control.Monad.when indexedWithFields $ do
          Control.Monad.unless (componentCount > 0) $
            unsupportedBecause "hidden-only telescope"
          Control.Monad.unless (supportsIndexedFieldInjectivity ctel) $
            unsupportedBecause "support predicate"
          Control.Monad.unless (componentCount == size ctel - hiddenPrefixCount) $ unsupportedBecause "component count"
          prefixEqual <- forM (zip3 (take hiddenPrefixCount $ telToList ctel) hiddenPrefixArgs0 hiddenPrefixVArgs0) $ \ (dom, uj, vj) ->
            lift $
              addContext gamma $
                (noConstraints (equalTerm (snd $ unDom dom) (unArg uj) (unArg vj)) $> True)
                  `catchError` \ _ -> pure False
          Control.Monad.unless (and prefixEqual) $ unsupportedBecause "hidden prefix equality"
        Control.Monad.when (not indexedWithFields && not (isNonDependentTelescope ctel)) $
          unsupportedBecause "non-dependent telescope"

        aLType <- caseMaybeM (lift $ addContext gamma $ toLType a) (unsupportedBecause "toLType injectType") pure
        (componentFieldNames, componentLTys, useGeneratedProjections) <- if indexedWithFields then do
          (projNames, projTypes) <- lift $ defineInjectivityProjections gamma a ch ctel
          ltys <- forM (drop hiddenPrefixCount projTypes) $ \ dom ->
            caseMaybeM
              (lift $ addContext gamma $ addContext ("d" :: String, defaultDom a) $ toLType $ unDom dom)
              (unsupportedBecause "toLType generated projection")
              pure
          pure (drop hiddenPrefixCount projNames, ltys, True)
        else do
          Control.Monad.unless (length (conFields ch) == size ctel) $ unsupportedBecause "conFields unavailable"
          fieldLTys <- forM (telToList ctel) $ \ dom ->
            caseMaybeM (lift $ addContext gamma $ toLType $ snd $ unDom dom) (unsupportedBecause "toLType field") pure
          pure (drop hiddenPrefixCount $ map unArg $ conFields ch, drop hiddenPrefixCount fieldLTys, False)

        interval <- lift primIntervalType
        let gamma_phis = abstract gamma $ telFromList $
              map (defaultDom . (,interval) . ("phi" ++) . show) [0 .. phis - 1]
        working_tel <- abstract gamma_phis <$>
          cantTransport' (pathTelescope' (raise phis $ eqTel st) (raise phis $ eqLHS st) (raise phis $ eqRHS st))
        next_working_tel <- abstract gamma_phis <$>
          cantTransport' (pathTelescope' (raise phis $ eqTel next) (raise phis $ eqLHS next) (raise phis $ eqRHS next))

        let prefixCount = size gamma + phis + k
            (pre_tel, ppost_tel) = splitTelescopeAt prefixCount working_tel
            (_next_pre_tel, next_qpost_tel) = splitTelescopeAt prefixCount next_working_tel
            (_next_q_tel, _next_post_tel) = splitTelescopeAt componentCount next_qpost_tel
            working_args = teleArgs working_tel
            next_args    = teleArgs next_working_tel
            (pre_args0, ppost_args0) = splitAt prefixCount working_args
            (next_pre_args0, next_qpost_args0) = splitAt prefixCount next_args
            (next_q_args0, next_post_args0) = splitAt componentCount next_qpost_args0

        Control.Monad.unless (length next_q_args0 == componentCount) $ unsupportedBecause "next q args length"

        p_arg0 <- case ppost_args0 of
          p : _ -> pure p
          []    -> __IMPOSSIBLE__
        post_args0 <- case ppost_args0 of
          _ : xs -> pure xs
          []     -> __IMPOSSIBLE__
        post_abs0 <- case ppost_tel of
          ExtendTel _ post_abs -> pure post_abs
          EmptyTel             -> __IMPOSSIBLE__

        let aTerm0 = case aLType of
              LEl _ t -> t
            aLevel0 = case aLType of
              LEl l _ -> Level l

        reportSDoc "tc.lhs.unify.inv" 20 $ vcat
          [ "working tel:" <+> prettyTCM working_tel
          , "next working tel:" <+> prettyTCM next_working_tel
          , "ctel:" <+> addContext prefixTel (prettyTCM ctel)
          ]

        (tau, leftInv, phi) <- do
          addContext working_tel $ runNamesT [] $ do
            let
              raiseFrom :: Subst x => Telescope -> x -> x
              raiseFrom tel x = raise (size working_tel - size tel) x
              raiseFromScrut :: Subst x => x -> x
              raiseFromScrut x = raise (size working_tel - size gamma - 1) x
              phi0 = raiseFrom gamma_phis $ var 0
            u <- open . raiseFrom gamma . unArg $ u0
            v <- open . raiseFrom gamma . unArg $ v0
            phi <- open phi0
            aTerm <- open $ raiseFrom gamma aTerm0
            aLevel <- open $ raiseFrom gamma aLevel0
            iz <- cl (lift primIZero)
            pre_args <- open pre_args0
            post_abs <- open $ raiseFrom pre_tel post_abs0
            hiddenUArgs0 <- open $ map (raiseFrom gamma) hiddenPrefixArgs0
            componentUArgs <- mapM (open . raiseFrom gamma . unArg) componentUArgs0
            componentVArgs <- mapM (open . raiseFrom gamma . unArg) componentVArgs0
            gammaArgs0 <- open $ map (raiseFrom gamma) (teleArgs gamma)
            let
              projApp ai proj t
                | useGeneratedProjections = do
                    gammaArgs <- gammaArgs0
                    pure $ defApp proj [] (map Apply gammaArgs ++ [Apply $ Arg ai t])
                | otherwise =
                    pure $ defApp proj [] [Apply (Arg ai t)]
              decodeComponents hiddenArgs0 rhss qs = lam "i" $ \ i -> do
                hiddenArgs <- hiddenArgs0
                compArgs <- sequence $
                  zipWith4
                    (\ ai q uj rhs -> Arg ai <$> (q <@@> (uj, rhs, i)))
                    componentArgInfo qs componentUArgs rhss
                pure $ Con ch ConOSystem (map Apply $ hiddenArgs ++ compArgs)
              encodeComponents fieldData p0 p1 p = forM fieldData $ \ (ai, lAbs, tyAbs, uj, _vj, proj) -> do
                reflj <- lam "i" $ \ _ -> uj
                fam <- lam "i" $ \ i -> do
                  pi <- p <@@> (p0, p1, i)
                  rhs <- projApp ai proj pi
                  l <- absApp <$> lAbs <*> pure pi
                  ty <- absApp <$> tyAbs <*> pure pi
                  cty <- lam "j" $ \ _ -> pure ty
                  cl (lift primPathP) <#> pure l <@> pure cty <@> uj <@> pure rhs
                la <- lam "i" $ \ i -> do
                  pi <- p <@@> (p0, p1, i)
                  absApp <$> lAbs <*> pure pi
                cl (lift primTrans) <#> pure la <@> pure fam <@> pure iz <@> pure reflj

            fieldData <- if useGeneratedProjections then
              forM (zip4 componentLTys componentFieldNames (zip componentArgInfo componentUArgs) componentVArgs) $ \ (LEl l t, proj, (ai, uj), vj) -> do
                lAbs  <- open $ raiseFromScrut (Abs "d" (Level l))
                tyAbs <- open $ raiseFromScrut (Abs "d" t)
                pure (ai, lAbs, tyAbs, uj, vj, proj)
            else
              forM (zip4 componentLTys componentFieldNames (zip componentArgInfo componentUArgs) componentVArgs) $ \ (LEl l t, proj, (ai, uj), vj) -> do
                l  <- open $ raiseFrom gamma (Level l)
                ty <- open $ raiseFrom gamma t
                pure (ai, fmap (Abs "d" . raise 1) l, fmap (Abs "d" . raise 1) ty, uj, vj, proj)

            qterms <- encodeComponents fieldData u v =<< open (unArg p_arg0)
            decodeP <- decodeComponents hiddenUArgs0 componentVArgs (map pure qterms)
            leftInvP <- do
              p <- open $ unArg p_arg0
              base <- lam "j" $ \ _ -> u
              la <- lam "i" $ \ _ -> aLevel
              fam <- lam "r" $ \ r -> do
                pr <- p <@@> (u, v, r)
                let rhss = [ projApp ai proj pr | (ai, _, _, _, _, proj) <- fieldData ]
                part <- lam "j" $ \ j -> do
                  rij <- cl (lift primIMin) <@> r <@> j
                  p <@@> (u, pure pr, pure rij)
                qs <- encodeComponents fieldData u (pure pr) (pure part)
                dec <- decodeComponents hiddenUArgs0 rhss (map pure qs)
                cty <- lam "i" $ \ _ -> aTerm
                cl (lift primPathP) <#> aLevel <@> pure cty <@> pure dec <@> pure part
              cl (lift primTrans) <#> pure la <@> pure fam <@> pure iz <@> pure base

            p <- open $ unArg p_arg0
            delta <- bind "i" $ \ i -> do
              pi <- pure leftInvP <@@> (pure decodeP, p, cl (lift primINeg) <@> i)
              absApp <$> post_abs <*> pure pi

            tau_post <- lift $ cantTransport (transpTel' True delta phi0 post_args0)
            post_fill <- bind "i" $ \ i -> do
              ni <- cl (lift primINeg) <@> i
              lift $ cantTransport (trFillTel' True delta phi0 post_args0 ni)
            post_fill <- open post_fill

            pre_tau <- pre_args
            let tauArgs = pre_tau ++ zipWith (\ arg q -> q <$ arg) next_q_args0 qterms ++ tau_post
            leftInvArgs <- fmap absBody $ bind "i" $ \ i -> do
              pre_i <- pre_args
              post_i <- lazyAbsApp <$> post_fill <*> i
              pi <- pure leftInvP <@@> (pure decodeP, p, i)
              pure $ pre_i ++ [pi <$ p_arg0] ++ post_i
            pure (termsS __IMPOSSIBLE__ $ map unArg tauArgs, termsS __IMPOSSIBLE__ $ map unArg leftInvArgs, phi0)

        rho <- addContext next_working_tel $ runNamesT [] $ do
          let
            raiseFromNext :: Subst x => Telescope -> x -> x
            raiseFromNext tel x = raise (size next_working_tel - size tel) x
          next_pre_args <- open next_pre_args0
          next_post_args <- open next_post_args0
          hiddenUArgs0 <- open $ map (raiseFromNext gamma) hiddenPrefixArgs0
          componentUArgs <- mapM (open . raiseFromNext gamma . unArg) componentUArgs0
          componentVArgs <- mapM (open . raiseFromNext gamma . unArg) componentVArgs0
          let decodeNext hiddenArgs0 rhss qs = lam "i" $ \ i -> do
                hiddenArgs <- hiddenArgs0
                args <- sequence $
                  zipWith4
                    (\ ai q uj rhs -> Arg ai <$> (q <@@> (uj, rhs, i)))
                    componentArgInfo qs componentUArgs rhss
                pure $ Con ch ConOSystem (map Apply $ hiddenArgs ++ args)
          pre_i <- next_pre_args
          qs <- mapM (open . unArg) next_q_args0
          post_i <- next_post_args
          p <- decodeNext hiddenUArgs0 componentVArgs qs
          pure $ termsS __IMPOSSIBLE__ $ map unArg pre_i ++ [p] ++ map unArg post_i

        return $ ((working_tel, rho, tau, leftInv), phi)
buildEquiv (DUnificationStep st step@(DEtaExpandVar fv _d _args) output) next = runExceptT $ do
        reportSDoc "tc.lhs.unify.inv" 20 "buildEquiv EtaExpandVar"
        let
          gamma = varTel st
          eqs = eqTel st
          x = flexVar fv
          neqs = size eqs
          phis = 1
        interval <- lift primIntervalType
         -- Γ, φs : I^phis
        let gamma_phis = abstract gamma $ telFromList $
              map (defaultDom . (,interval) . ("phi" ++) . show) [0 .. phis - 1]
        working_tel <- abstract gamma_phis <$> do
         withExceptT CantTransport' $
          pathTelescope' (raise phis $ eqTel st) (raise phis $ eqLHS st) (raise phis $ eqRHS st)
        let raiseFrom tel x = (size working_tel - size tel) + x
        let phi = var $ raiseFrom gamma_phis 0

        caseMaybeM (expandRecordVar (raiseFrom gamma x) working_tel) __IMPOSSIBLE__ $ \ (_,tau,rho,_) -> do
          reportSDoc "tc.lhs.unify.inv" 20 $ addContext working_tel $ "tau    :" <+> prettyTCM tau
          return $ ((working_tel,rho,tau,raiseS 1),phi)


{-# SPECIALIZE explainStep :: UnifyStep -> TCM Doc #-}
explainStep :: MonadPretty m => UnifyStep -> m Doc
explainStep Injectivity{injectConstructor = ch} =
  "injectivity of the data constructor" <+> prettyTCM (conName ch)
explainStep TypeConInjectivity{} = "injectivity of type constructors"
explainStep Deletion{}           = "the K rule"
explainStep Solution{}           = "substitution in Setω"
-- Note: this is the actual reason that a Solution step can fail, rather
-- than the explanation for the actual step
explainStep Conflict{}          = "the disjointness of data constructors"
explainStep LitConflict{}       = "the disjointness of literal values"
explainStep Cycle{}             = "the impossibility of cyclic values"
explainStep EtaExpandVar{}      = "eta-expansion of variables"
explainStep EtaExpandEquation{} = "eta-expansion of equations"
explainStep StripSizeSuc{}      = "the injectivity of size successors"
explainStep SkipIrrelevantEquation{} = "ignoring irrelevant equations"
