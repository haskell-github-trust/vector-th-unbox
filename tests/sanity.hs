{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main (main) where

import Prelude
import Data.Default
#if __GLASGOW_HASKELL__ == 704
import qualified Data.Vector.Generic
import qualified Data.Vector.Generic.Mutable
#endif
import Data.Vector.Unboxed.Base (Unbox)
import Data.Vector.Unboxed.Deriving

derivingUnbox "Maybe"
    [t| ∀ a. (Default a, Unbox a) ⇒ Maybe a → (Bool, a) |]
    [| maybe (False, def) (\ x → (True, x)) |]
    [| \ (b, x) → if b then Just x else Nothing |]

main ∷ IO ()
main = return ()

