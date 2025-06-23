
module Text.PrettyPrint where

open import Data.Unit
import Text.PrettyPrint.Annotated as Ann

open Ann public hiding (Doc; Pretty)

Doc = Ann.Doc ⊤

Pretty : ∀ {l} {A : Set l} → Set l → Set l
Pretty = Ann.Pretty ⊤
