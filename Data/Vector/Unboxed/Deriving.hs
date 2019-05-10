{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

{-|
Module:      Data.Vector.Unboxed.Deriving
Copyright:   © 2012−2015 Liyang HU
License:     BSD3
Maintainer:  vector-th-unbox@liyang.hu
Stability:   experimental
Portability: non-portable
-}

module Data.Vector.Unboxed.Deriving
    ( -- $usage
      derivingUnbox
    ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Arrow
import Control.Monad
import Data.Char (isAlphaNum)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as M
import Data.Vector.Unboxed.Base (MVector (..), Vector (..), Unbox)
import Language.Haskell.TH

-- Create a @Pat@ bound to the given name and an @Exp@ for said binding.
newPatExp :: String -> Q (Pat, Exp)
newPatExp = fmap (VarP &&& VarE) . newName

data Common = Common
    { mvName, vName :: Name
    , i, n, mv, mv', v :: (Pat, Exp) }

common :: String -> Q Common
common name = do
    -- A bit looser than “Haskell 2010: §2.4 Identifiers and Operators”…
    let valid c = c == '_' || c == '\'' || c == '#' || isAlphaNum c
    unless (all valid name) $ do
        fail (show name ++ " is not a valid constructor suffix!")
    let mvName = mkName ("MV_" ++ name)
    let vName = mkName ("V_" ++ name)
    i <- newPatExp "idx"
    n <- newPatExp "len"
    mv  <- first (ConP mvName . (:[])) <$> newPatExp "mvec"
    mv' <- first (ConP mvName . (:[])) <$> newPatExp "mvec'"
    v   <- first (ConP vName  . (:[])) <$> newPatExp "vec"
    return Common {..}

-- Turn any 'Name' into a capturable one.
capture :: Name -> Name
#if __GLASGOW_HASKELL__ == 704
capture = mkName . nameBase
#else
capture = id
#endif

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
>    [t| ∀ a. (Default a, Unbox a) ⇒ Maybe a → (Bool, a) |]
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
    a <- second (AppE toRep) <$> newPatExp "val"
    args <- argsQ
    (cxts, typ, rep) <- case args of
        ForallT _ cxts (ArrowT `AppT` typ `AppT` rep) -> return (cxts, typ, rep)
        ArrowT `AppT` typ `AppT` rep -> return ([], typ, rep)
        _ -> fail "Expecting a type of the form: cxts => typ -> rep"

    let s = VarT (mkName "s")
#if MIN_VERSION_template_haskell(2,11,0)
    let lazy = Bang NoSourceUnpackedness NoSourceStrictness
# define MAYBE_KIND Nothing
# define MAYBE_OVERLAP Nothing
#else
    let lazy = NotStrict
# define MAYBE_KIND
# define MAYBE_OVERLAP
#endif
#if MIN_VERSION_template_haskell(2,15,0)
    newtypeMVector <- do
        tmp <- [t|MVector $(return s) $(return typ)|]
        return $ NewtypeInstD [] Nothing tmp MAYBE_KIND
            (NormalC mvName [(lazy, ConT ''MVector `AppT` s `AppT` rep)]) []
#else
    let newtypeMVector = NewtypeInstD [] ''MVector [s, typ] MAYBE_KIND []
            (NormalC mvName [(lazy, ConT ''MVector `AppT` s `AppT` rep)]) []
#endif
    let mvCon = ConE mvName
    let instanceMVector = InstanceD MAYBE_OVERLAP cxts
            (ConT ''M.MVector `AppT` ConT ''MVector `AppT` typ) $ concat
            [ wrap 'M.basicLength           [mv]        id
            , wrap 'M.basicUnsafeSlice      [i, n, mv]  (AppE mvCon)
            , wrap 'M.basicOverlaps         [mv, mv']   id
            , wrap 'M.basicUnsafeNew        [n]         (liftE mvCon)
#if MIN_VERSION_vector(0,11,0)
            , wrap 'M.basicInitialize       [mv]        id
#endif
            , wrap 'M.basicUnsafeReplicate  [n, a]      (liftE mvCon)
            , wrap 'M.basicUnsafeRead       [mv, i]     (liftE fromRep)
            , wrap 'M.basicUnsafeWrite      [mv, i, a]  id
            , wrap 'M.basicClear            [mv]        id
            , wrap 'M.basicSet              [mv, a]     id
            , wrap 'M.basicUnsafeCopy       [mv, mv']   id
            , wrap 'M.basicUnsafeMove       [mv, mv']   id
            , wrap 'M.basicUnsafeGrow       [mv, n]     (liftE mvCon) ]

#if MIN_VERSION_template_haskell(2,15,0)
    newtypeVector <- do
        tmp <- [t|Vector $(return typ)|]
        return $ NewtypeInstD [] Nothing tmp MAYBE_KIND
            (NormalC vName [(lazy, ConT ''Vector `AppT` rep)]) []
#else
    let newtypeVector = NewtypeInstD [] ''Vector [typ] MAYBE_KIND
            (NormalC vName [(lazy, ConT ''Vector `AppT` rep)]) []
#endif
    let vCon  = ConE vName
    let instanceVector = InstanceD MAYBE_OVERLAP cxts
            (ConT ''G.Vector `AppT` ConT ''Vector `AppT` typ) $ concat
            [ wrap 'G.basicUnsafeFreeze     [mv]        (liftE vCon)
            , wrap 'G.basicUnsafeThaw       [v]         (liftE mvCon)
            , wrap 'G.basicLength           [v]         id
            , wrap 'G.basicUnsafeSlice      [i, n, v]   (AppE vCon)
            , wrap 'G.basicUnsafeIndexM     [v, i]      (liftE fromRep)
            , wrap 'G.basicUnsafeCopy       [mv, v]     id
            , wrap 'G.elemseq               [v, a]      id ]

    return [ InstanceD MAYBE_OVERLAP cxts (ConT ''Unbox `AppT` typ) []
        , newtypeMVector, instanceMVector
        , newtypeVector, instanceVector ]

#undef __GLASGOW_HASKELL__
{-$usage

Writing @Unbox@ instances for new data types is tedious and formulaic. More
often than not, there is a straightforward mapping of the new type onto some
existing one already imbued with an @Unbox@ instance. The
<http://hackage.haskell.org/package/vector/docs/Data-Vector-Unboxed.html example>
from the @vector@ package represents @Complex a@ as pairs @(a, a)@. Using
'derivingUnbox', we can define the same instances much more succinctly:

>derivingUnbox "Complex"
>    [t| ∀ a. (Unbox a) ⇒ Complex a → (a, a) |]
>    [| \ (r :+ i) → (r, i) |]
>    [| \ (r, i) → r :+ i |]

Requires the @MultiParamTypeClasses@, @TemplateHaskell@, @TypeFamilies@ and
probably the @FlexibleInstances@ @LANGUAGE@ extensions. Note that GHC 7.4
(but not earlier nor later) needs the 'G.Vector' and 'M.MVector' class
method names to be in scope in order to define the appropriate instances:

>#if __GLASGOW_HASKELL__ == 704
>import qualified Data.Vector.Generic
>import qualified Data.Vector.Generic.Mutable
>#endif

Consult the <https://github.com/liyang/vector-th-unbox/blob/master/tests/sanity.hs sanity test>
for a working example.

-}

