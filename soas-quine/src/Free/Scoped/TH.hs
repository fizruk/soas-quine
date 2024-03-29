-- copied from https://github.com/rzk-lang/rzk/blob/7d42ef6267a42fcd4577228ef56f4d3749d5d2be/rzk/src/Free/Scoped/TH.hs
{-# LANGUAGE CPP             #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module Free.Scoped.TH where

import           Control.Monad       (replicateM)
import           Free.Scoped
import           Language.Haskell.TH

mkConP :: Name -> [Pat] -> Pat
#if __GLASGOW_HASKELL__ >= 902
mkConP name pats = ConP name [] pats
#else
mkConP name pats = ConP name pats
#endif

makePatternsAll :: Name -> Q [Dec]
makePatternsAll ty = do
  TyConI tyCon <- reify ty
  case tyCon of
    DataD _ tyName typeParams _ cs _ -> concat <$> do
      let typeParamName = \case
            PlainTV name _ -> name
            KindedTV name _ _ -> name
      var <- newName "var"
      let [scope, term] = map typeParamName (reverse (take 2 (reverse typeParams)))
          paramNames = map typeParamName (reverse (drop 2 (reverse typeParams)))
          ast = AppT (ConT ''FS) (foldl AppT (ConT tyName) (fmap VarT paramNames))
      xs <- mapM (makePatternFor ast scope term var) cs
      xs' <- makeCompletePragma cs
      ys <- mapM makePatternEFor cs
      ys' <- makeCompletePragmaE cs
      zs <- mapM makePatternTFor cs
      zs' <- makeCompletePragmaT cs
      ws <- mapM makePatternTEFor cs
      ws' <- makeCompletePragmaTE cs
      return (xs ++ [xs'] ++ ys ++ [ys'] ++ zs ++ [zs'] ++ ws ++ [ws'])

    _                  -> fail "Can only make patterns for data types."


makeCompletePragma :: [Con] -> Q [Dec]
makeCompletePragma cs = do
  DataConI varName _ _ <- reify 'Pure
  let names = [mkName (removeF (nameBase name)) | NormalC name _ <- cs]
  return [PragmaD (CompleteP (varName : names) Nothing)]
  where
    removeF s = take (length s - 1) s

makeCompletePragmaE :: [Con] -> Q [Dec]
makeCompletePragmaE cs = do
  DataConI varName _ _ <- reify 'Pure
  PatSynI extName _ <- reify 'ExtE
  let names = [mkName (removeF (nameBase name)) | NormalC name _ <- cs]
  return [PragmaD (CompleteP (varName : extName : names) Nothing)]
  where
    removeF s = take (length s - 1) s <> "E"

makeCompletePragmaT :: [Con] -> Q [Dec]
makeCompletePragmaT cs = do
  DataConI varName _ _ <- reify 'Pure
  let names = [mkName (removeF (nameBase name)) | NormalC name _ <- cs]
  return [PragmaD (CompleteP (varName : names) Nothing)]
  where
    removeF s = take (length s - 1) s <> "T"

makeCompletePragmaTE :: [Con] -> Q [Dec]
makeCompletePragmaTE cs = do
  DataConI varName _ _ <- reify 'Pure
  let names = [mkName (removeF (nameBase name)) | NormalC name _ <- cs]
  return [PragmaD (CompleteP (varName : names) Nothing)]
  where
    removeF s = take (length s - 1) s <> "TE"

makePatternFor :: Type -> Name -> Name -> Name -> Con -> Q [Dec]
makePatternFor ast scope term var = \case
  NormalC name xs -> do
    args <- replicateM (length xs) (newName "x")
    let patArgTypes = map (toPatArgType var . snd) xs
    let patName = mkName (removeF (nameBase name))
        patArgs = PrefixPatSyn args
        dir = ImplBidir
    pat <- [p| Free $(pure (mkConP name (VarP <$> args))) |]
    return
      [ PatSynSigD patName (foldr (AppT . AppT ArrowT) (AppT ast (VarT var)) patArgTypes)
      , PatSynD patName patArgs dir pat
      ]
  _ -> fail "Can only make patterns for NormalC constructors"
  where
    removeF s = take (length s - 1) s

    toPatArgType var = \case
      VarT name
        | name == scope -> AppT ast (AppT (ConT ''Inc) (VarT var))
        | name == term  -> AppT ast (VarT var)
      t -> t

makePatternEFor :: Con -> Q [Dec]
makePatternEFor = \case
  NormalC name xs -> do
    args <- replicateM (length xs) (newName "x")
    let patName = mkName (removeF (nameBase name))
        patArgs = PrefixPatSyn args
        dir = ImplBidir
    pat <- [p| Free (InL $(pure (mkConP name (VarP <$> args)))) |]
    return [PatSynD patName patArgs dir pat]
  _ -> fail "Can only make patterns for NormalC constructors"
  where
    removeF s = take (length s - 1) s <> "E"

makePatternTFor :: Con -> Q [Dec]
makePatternTFor = \case
  NormalC name xs -> do
    t <- newName "type_"
    args <- replicateM (length xs) (newName "x")
    let patName = mkName (removeF (nameBase name))
        patArgs = PrefixPatSyn (t : args)
        dir = ImplBidir
    pat <- [p| Free (AnnF $(pure (VarP t)) $(pure (mkConP name (VarP <$> args)))) |]
    return [PatSynD patName patArgs dir pat]
  _ -> fail "Can only make patterns for NormalC constructors"
  where
    removeF s = take (length s - 1) s <> "T"

makePatternTEFor :: Con -> Q [Dec]
makePatternTEFor = \case
  NormalC name xs -> do
    t <- newName "type_"
    args <- replicateM (length xs) (newName "x")
    let patName = mkName (removeF (nameBase name))
        patArgs = PrefixPatSyn (t : args)
        dir = ImplBidir
    pat <- [p| Free (InL (AnnF $(pure (VarP t)) $(pure (mkConP name (VarP <$> args))))) |]
    return [PatSynD patName patArgs dir pat]
  _ -> fail "Can only make patterns for NormalC constructors"
  where
    removeF s = take (length s - 1) s <> "TE"
