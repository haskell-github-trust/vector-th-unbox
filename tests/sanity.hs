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
import Data.Default
import qualified Data.Vector.Generic
import qualified Data.Vector.Generic.Mutable
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving

derivingUnbox "Maybe"
    [t| (Default a, Unbox a) ⇒ Maybe a → (Bool, a) |]
    [| maybe (False, def) (\ x → (True, x)) |]
    [| \ (b, x) → if b then Just x else Nothing |]

main ∷ IO ()
main = return ()

