{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

{-|
Module:      Data.Vector.Unboxed.Deriving
Copyright:   © Liyang HU 2012
License:     BSD3
Maintainer:  vector-th-unbox@liyang.hu
Stability:   experimental
Portability: non-portable

Writing @Unbox@ instances for new data types is tedious and formulaic. More
often than not, there is a straightforward mapping of the new type onto some
existing one already imbued with an @Unbox@ instance. The example from the
@vector@ package represents @Complex a@ as pairs @(a, a)@. (See
<http://hackage.haskell.org/packages/archive/vector/latest/doc/html/Data-Vector-Unboxed.html>.)
Using 'derivingUnbox', we can define the same instances much more
succinctly:

>derivingUnbox "Complex"
>    [t| (Unbox a) ⇒ Complex a → (a, a) |]
>    [| \ (r :+ i) → (r, i) |]
>    [| \ (r, i) → r :+ i |]

Requires the @MultiParamTypeClasses@, @TemplateHaskell@, @TypeFamilies@ and
probably the @FlexibleInstances@ @LANGUAGE@ extensions. Older versions of
GHC needs the 'G.Vector' and 'M.MVector' class method names in scope:

>import qualified Data.Vector.Generic
>import qualified Data.Vector.Generic.Mutable

-}

module Data.Vector.Unboxed.Deriving (derivingUnbox) where

import Control.Arrow
import Control.Applicative
import Control.Monad
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as M
import Data.Vector.Unboxed.Base (MVector (..), Vector (..), Unbox)
import Language.Haskell.TH

-- Create a @Pat@ bound to the given name and an @Exp@ for said binding.
newPatExp :: String -> Q (Pat, Exp)
newPatExp = fmap (VarP &&& VarE) . newName

-- Create a wrapper for the given function with the same 'nameBase', given
-- a list of argument bindings and expressions in terms of said bindings.
-- A final coercion (@Exp → Exp@) is applied to the body of the function.
-- Complimentary @INLINE@ pragma included.
wrap :: Name -> [(Pat, Exp)] -> (Exp -> Exp) -> [Dec]
wrap fun (unzip -> (pats, exps)) coerce = [inline, method] where
#if MIN_VERSION_template_haskell(2,8,0)
    inline = PragmaD (InlineP fun Inline FunLike AllPhases)
#else
    inline = PragmaD ( InlineP (mkName (nameBase fun))
        (InlineSpec True False Nothing) )
#endif
    body = coerce $ foldl AppE (VarE fun) exps
    method = FunD fun [Clause pats (NormalB body) []]

{-| Let's consider a more complex example: suppose we want an @Unbox@
instance for @Maybe a@. We can encode this using the pair @(Bool, a)@, with
the boolean indicating whether we have @Nothing@ or @Just@ something. This
encoding requires a dummy value in the @Nothing@ case, necessitating an
additional @Default@ (see the @data-default@ package) constraint. Thus:

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
    let mvName = mkName ("MV_" ++ name)
    let vName  = mkName ("V_" ++ name)
    toRep <- toRepQ
    fromRep <- fromRepQ
    args <- argsQ
    (cxts, typ, rep) <- case args of
        ForallT _ cxts (ArrowT `AppT` typ `AppT` rep) -> return (cxts, typ, rep)
        ArrowT `AppT` typ `AppT` rep -> return ([], typ, rep)
        _ -> fail "Expecting a type of the form: cxts => typ -> rep"

    let liftE e = InfixE (Just e) (VarE 'liftM) . Just
    let mvCon = ConE mvName
    let vCon  = ConE vName
    i <- newPatExp "idx"
    n <- newPatExp "len"
    a <- second (AppE toRep) <$> newPatExp "val"
    mv  <- first (ConP mvName . (:[])) <$> newPatExp "mvec"
    mv' <- first (ConP mvName . (:[])) <$> newPatExp "mvec'"
    v   <- first (ConP vName  . (:[])) <$> newPatExp "vec"

    s <- VarT <$> newName "s"
    let newtypeMVector = NewtypeInstD [] ''MVector [s, typ]
            (NormalC mvName [(NotStrict, ConT ''MVector `AppT` s `AppT` rep)]) []
    let instanceMVector = InstanceD cxts
            (ConT ''M.MVector `AppT` ConT ''MVector `AppT` typ) $ concat
            [ wrap 'M.basicLength           [mv]        id
            , wrap 'M.basicUnsafeSlice      [i, n, mv]  (AppE mvCon)
            , wrap 'M.basicOverlaps         [mv, mv']   id
            , wrap 'M.basicUnsafeNew        [n]         (liftE mvCon)
            , wrap 'M.basicUnsafeReplicate  [n, a]      (liftE mvCon)
            , wrap 'M.basicUnsafeRead       [mv, i]     (liftE fromRep)
            , wrap 'M.basicUnsafeWrite      [mv, i, a]  id
            , wrap 'M.basicClear            [mv]        id
            , wrap 'M.basicSet              [mv, a]     id
            , wrap 'M.basicUnsafeCopy       [mv, mv']   id
            , wrap 'M.basicUnsafeGrow       [mv, n]     (liftE mvCon) ]

    let newtypeVector = NewtypeInstD [] ''Vector [typ]
            (NormalC vName [(NotStrict, ConT ''Vector `AppT` rep)]) []
    let instanceVector = InstanceD cxts
            (ConT ''G.Vector `AppT` ConT ''Vector `AppT` typ) $ concat
            [ wrap 'G.basicUnsafeFreeze     [mv]        (liftE vCon)
            , wrap 'G.basicUnsafeThaw       [v]         (liftE mvCon)
            , wrap 'G.basicLength           [v]         id
            , wrap 'G.basicUnsafeSlice      [i, n, v]   (AppE vCon)
            , wrap 'G.basicUnsafeIndexM     [v, i]      (liftE fromRep)
            , wrap 'G.basicUnsafeCopy       [mv, v]     id
            , wrap 'G.elemseq               [v, a]      id ]

    return [ InstanceD cxts (ConT ''Unbox `AppT` typ) []
        , newtypeMVector, instanceMVector
        , newtypeVector, instanceVector ]

