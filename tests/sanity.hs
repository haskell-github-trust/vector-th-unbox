{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 706
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#endif

module Main (main) where

import Prelude
import Control.Monad
import Data.Default
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as M
import qualified Data.Vector.Unboxed as VU
import Data.Vector.Unboxed.Base (MVector (MV_3), Vector (V_3), Unbox)
import Data.Vector.Unboxed.Deriving

derivingUnbox "Maybe"
    [t| (Default a, Unbox a) ⇒ Maybe a → (Bool, a) |]
    [| maybe (False, def) (\ x → (True, x)) |]
    [| \ (b, x) → if b then Just x else Nothing |]

-- Must splice in newtypes before we can quote @MV_Either@ or @V_Either@.
newtypeUnboxCustom "Either"
    [t| (Unbox a, Unbox b) ⇒ Either a b → (Bool, a, b) |]
derivingUnboxCustom "Either"
    [t| (Unbox a, Unbox b) ⇒ Either a b → (Bool, a, b) |]
    [d|
        -- Default basicUnsafeReplicate calls basicSet; good enough.
        {-# INLINE basicUnsafeRead #-}
        basicUnsafeRead (MV_Either (MV_3 _n ve va vb)) i = do
            e <- M.basicUnsafeRead ve i
            case e of
                False -> Left `liftM` M.basicUnsafeRead va i
                True -> Right `liftM` M.basicUnsafeRead vb i
        {-# INLINE basicUnsafeWrite #-}
        basicUnsafeWrite (MV_Either (MV_3 _n ve va vb)) i = either
            (\ a -> M.basicUnsafeWrite ve i False >> M.basicUnsafeWrite va i a)
            (\ b -> M.basicUnsafeWrite ve i True  >> M.basicUnsafeWrite vb i b)
        {-# INLINE basicSet #-}
        basicSet (MV_Either (MV_3 _n ve va vb)) = either
            (\ a -> M.basicSet ve False >> M.basicSet va a)
            (\ b -> M.basicSet ve True  >> M.basicSet vb b)
    |] [d|
        {-# INLINE basicUnsafeIndexM #-}
        basicUnsafeIndexM (V_Either (V_3 _n ve va vb)) i = do
            e <- G.basicUnsafeIndexM ve i
            case e of
                False -> Left `liftM` G.basicUnsafeIndexM va i
                True -> Right `liftM` G.basicUnsafeIndexM vb i
        {-# INLINE elemseq #-}
        elemseq _ = either
            (G.elemseq (undefined :: VU.Vector a))
            (G.elemseq (undefined :: VU.Vector b))
    |]

main ∷ IO ()
main = return ()

