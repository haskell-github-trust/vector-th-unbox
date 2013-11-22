{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

{-|
Module:      Data.Vector.Unboxed.Deriving
Copyright:   © 2012−2013 Liyang HU
License:     BSD3
Maintainer:  vector-th-unbox@liyang.hu
Stability:   experimental
Portability: non-portable

Writing @Unbox@ instances for new data types is tedious and formulaic. More
often than not, there is a straightforward mapping of the new type onto some
existing one already imbued with an @Unbox@ instance. The
<http://hackage.haskell.org/package/vector/docs/Data-Vector-Unboxed.html example>
from the @vector@ package represents @Complex a@ as pairs @(a, a)@. Using
'derivingUnbox', we can define the same instances much more succinctly:

>derivingUnbox "Complex"
>    [t| (Unbox a) ⇒ Complex a → (a, a) |]
>    [| \ (r :+ i) → (r, i) |]
>    [| \ (r, i) → r :+ i |]

Requires the @MultiParamTypeClasses@, @TemplateHaskell@, @TypeFamilies@ and
probably the @FlexibleInstances@ @LANGUAGE@ extensions. Note that GHC 7.4
(but not earlier nor later) needs the 'G.Vector' and 'M.MVector' class
method names to be in scope in order to define the appropriate instances:

>#if __GLASGOW_HASKELL == 704
>import qualified Data.Vector.Generic
>import qualified Data.Vector.Generic.Mutable
>#endif

Consult the <https://github.com/liyang/vector-th-unbox/blob/master/tests/sanity.hs sanity test>
for a working example.
-}

module Data.Vector.Unboxed.Deriving (derivingUnbox, newtypeUnboxCustom, derivingUnboxCustom) where

import Control.Arrow
import Control.Applicative
import Control.Monad
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as M
import Data.Vector.Unboxed.Base (MVector (..), Vector (..), Unbox)
import Language.Haskell.TH

consUnbox :: String -> (Name, Name)
consUnbox name = (mkName $ "MV_" ++ name, mkName $ "V_" ++ name)

-- Create a @Pat@ bound to the given name and an @Exp@ for said binding.
newPatExp :: String -> Q (Pat, Exp)
newPatExp = fmap (VarP &&& VarE) . newName

data Common = Common
    { mvName, vName :: Name
    , i, n, mv, mv', v :: (Pat, Exp) }

common :: String -> Q Common
common name = do
    let (mvName, vName) = consUnbox name
    i <- newPatExp "idx"
    n <- newPatExp "len"
    mv  <- first (ConP mvName . (:[])) <$> newPatExp "mvec"
    mv' <- first (ConP mvName . (:[])) <$> newPatExp "mvec'"
    v   <- first (ConP vName  . (:[])) <$> newPatExp "vec"
    return Common {..}

-- Turn any 'Name' into a capturable one.
capture :: Name -> Name
capture = mkName . nameBase

liftE :: Exp -> Exp -> Exp
liftE e = InfixE (Just e) (VarE 'liftM) . Just

-- Create a wrapper for the given function with the same 'nameBase', given
-- a list of argument bindings and expressions in terms of said bindings.
-- A final coercion (@Exp → Exp@) is applied to the body of the function.
-- Complimentary @INLINE@ pragma included.
wrap :: Name -> [(Pat, Exp)] -> (Exp -> Exp) -> [Dec]
wrap fun (unzip -> (pats, exps)) coerce = [inline, method] where
    name = capture fun
#if MIN_VERSION_template_haskell(2,8,0)
    inline = PragmaD (InlineP name Inline FunLike AllPhases)
#else
    inline = PragmaD ( InlineP name (InlineSpec True False Nothing) )
#endif
    body = coerce $ foldl AppE (VarE fun) exps
    method = FunD name [Clause pats (NormalB body) []]

{-| Let's consider a more complex example: suppose we want an @Unbox@
instance for @Maybe a@. We could encode this using the pair @(Bool, a)@,
with the boolean indicating whether we have @Nothing@ or @Just@ something.
This encoding requires a dummy value in the @Nothing@ case, necessitating an
additional <http://hackage.haskell.org/package/data-default/docs/Data-Default.html#t:Default Default>
constraint. Thus:

>derivingUnbox "Maybe"
>    [t| (Default a, Unbox a) ⇒ Maybe a → (Bool, a) |]
>    [| maybe (False, def) (\ x → (True, x)) |]
>    [| \ (b, x) → if b then Just x else Nothing |]
-}
derivingUnbox
    :: String   -- ^ Unique constructor suffix for the MVector and Vector data families
    -> TypeQ    -- ^ Quotation of the form @[t| /ctxt/ ⇒ src → rep |]@
    -> ExpQ     -- ^ Quotation of an expression of type @src → rep@
    -> ExpQ     -- ^ Quotation of an expression of type @rep → src@
    -> DecsQ    -- ^ Declarations to be spliced for the derived Unbox instance
derivingUnbox name argsQ toRepQ fromRepQ = do
    Common {..} <- common name
    toRep <- toRepQ
    fromRep <- fromRepQ
    x <- second (AppE toRep) <$> newPatExp "val"

    let customMV = concat
            [ wrap 'M.basicUnsafeReplicate  [n, x]      (liftE $ ConE mvName)
            , wrap 'M.basicUnsafeRead       [mv, i]     (liftE fromRep)
            , wrap 'M.basicUnsafeWrite      [mv, i, x]  id
            , wrap 'M.basicSet              [mv, x]     id ]
    let customV = concat
            [ wrap 'G.basicUnsafeIndexM     [v, i]      (liftE fromRep)
            , wrap 'G.elemseq               [v, x]      id ]

    (++) <$> newtypeUnboxCustom name argsQ
        <*> derivingUnboxCustom name argsQ (return customMV) (return customV)

-- When the user writes @[d| foo = bar |]@, TH creates a unique local name
-- for 'foo' (with the @NameU@ @NameFlavour@; see source code for 'Name'.)
-- Since we're expecting the user to give instance method declarations, we
-- actually do want capturable names.
captureDecs :: [Dec] -> [Dec]
captureDecs = map $ \ d -> case d of
    FunD name clauses -> FunD (capture name) clauses
#if MIN_VERSION_template_haskell(2,8,0)
    PragmaD (InlineP name il rm ph) -> PragmaD (InlineP (capture name) il rm ph)
#else
    PragmaD (InlineP name is) -> PragmaD (InlineP (capture name) is)
#endif
    _ -> d

{-| If the 'Default' constraint or the overhead in the 'Nothing' case is
unacceptable, we can alternatively give only those methods that actually
deal with values of the type that we are trying to 'Unbox'; those that don't
are automatically generated as wrappers around the corresponding methods for
the representation. Suppose now we want to 'Unbox' 'Either':

>-- Must splice in newtypes before we can quote @MV_Either@ or @V_Either@.
>newtypeUnboxCustom "Either"
>    [t| (Unbox a, Unbox b) ⇒ Either a b → (Bool, a, b) |]
>derivingUnboxCustom "Either"
>    [t| (Unbox a, Unbox b) ⇒ Either a b → (Bool, a, b) |]
>    [d|
>        -- Default basicUnsafeReplicate calls basicSet; good enough.
>        {-# INLINE basicUnsafeRead #-}
>        basicUnsafeRead (MV_Either (MV_3 _n ve va vb)) i = do
>            e <- M.basicUnsafeRead ve i
>            case e of
>                False -> Left `liftM` M.basicUnsafeRead va i
>                True -> Right `liftM` M.basicUnsafeRead vb i
>        {-# INLINE basicUnsafeWrite #-}
>        basicUnsafeWrite (MV_Either (MV_3 _n ve va vb)) i = either
>            (\ a -> M.basicUnsafeWrite ve i False >> M.basicUnsafeWrite va i a)
>            (\ b -> M.basicUnsafeWrite ve i True  >> M.basicUnsafeWrite vb i b)
>        {-# INLINE basicSet #-}
>        basicSet (MV_Either (MV_3 _n ve va vb)) = either
>            (\ a -> M.basicSet ve False >> M.basicSet va a)
>            (\ b -> M.basicSet ve True  >> M.basicSet vb b)
>    |] [d|
>        {-# INLINE basicUnsafeIndexM #-}
>        basicUnsafeIndexM (V_Either (V_3 _n ve va vb)) i = do
>            e <- G.basicUnsafeIndexM ve i
>            case e of
>                False -> Left `liftM` G.basicUnsafeIndexM va i
>                True -> Right `liftM` G.basicUnsafeIndexM vb i
>        {-# INLINE elemseq #-}
>        elemseq _ = either
>            (G.elemseq (undefined :: VU.Vector a))
>            (G.elemseq (undefined :: VU.Vector b))
>    |]
-}

parseArgs :: TypeQ -> Q (Cxt, Type, Type)
parseArgs argsQ = do
    args <- argsQ
    case args of
        ForallT _ cxts (ArrowT `AppT` typ `AppT` rep) -> return (cxts, typ, rep)
        ArrowT `AppT` typ `AppT` rep -> return ([], typ, rep)
        _ -> fail "Expecting a type of the form: cxts => typ -> rep"

newtypeUnboxCustom :: String -> TypeQ -> DecsQ
newtypeUnboxCustom name argsQ = do
    let (mvName, vName) = consUnbox name
    (_, typ, rep) <- parseArgs argsQ
    s <- VarT <$> newName "s"
    let newtypeMVector = NewtypeInstD [] ''MVector [s, typ]
            (NormalC mvName [(NotStrict, ConT ''MVector `AppT` s `AppT` rep)]) []
    let newtypeVector = NewtypeInstD [] ''Vector [typ]
            (NormalC vName [(NotStrict, ConT ''Vector `AppT` rep)]) []
    return [newtypeMVector, newtypeVector]

derivingUnboxCustom
    :: String   -- ^ Unique constructor suffix for the MVector and Vector data families
    -> TypeQ    -- ^ Quotation of the form @[t| /ctxt/ ⇒ src → rep |]@
    -> DecsQ    -- ^ Custom 'M.MVector' instance methods:
                -- 'M.basicUnsafeReplicate', 'M.basicUnsafeRead',
                -- 'M.basicUnsafeWrite', and 'M.basicSet'
    -> DecsQ    -- ^ Custom 'G.Vector' instance methods:
                -- 'G.basicUnsafeIndexM' and 'G.elemseq'
    -> DecsQ    -- ^ Declarations to be spliced for the derived Unbox instance
derivingUnboxCustom name argsQ customMVQ customVQ = do
    Common {..} <- common name
    (cxts, typ, _rep) <- parseArgs argsQ
    customMV <- captureDecs <$> customMVQ
    customV <- captureDecs <$> customVQ

    let mvCon = ConE mvName
    let instanceMVector = InstanceD cxts
            (ConT ''M.MVector `AppT` ConT ''MVector `AppT` typ) $ concat
            [ wrap 'M.basicLength           [mv]        id
            , wrap 'M.basicUnsafeSlice      [i, n, mv]  (AppE mvCon)
            , wrap 'M.basicOverlaps         [mv, mv']   id
            , wrap 'M.basicUnsafeNew        [n]         (liftE mvCon)
            , wrap 'M.basicClear            [mv]        id
            , wrap 'M.basicUnsafeCopy       [mv, mv']   id
            , wrap 'M.basicUnsafeMove       [mv, mv']   id
            , wrap 'M.basicUnsafeGrow       [mv, n]     (liftE mvCon)
            , customMV ]

    let vCon  = ConE vName
    let instanceVector = InstanceD cxts
            (ConT ''G.Vector `AppT` ConT ''Vector `AppT` typ) $ concat
            [ wrap 'G.basicUnsafeFreeze     [mv]        (liftE vCon)
            , wrap 'G.basicUnsafeThaw       [v]         (liftE mvCon)
            , wrap 'G.basicLength           [v]         id
            , wrap 'G.basicUnsafeSlice      [i, n, v]   (AppE vCon)
            , wrap 'G.basicUnsafeCopy       [mv, v]     id
            , customV ]

    return [ instanceMVector, instanceVector
        , InstanceD cxts (ConT ''Unbox `AppT` typ) [] ]

