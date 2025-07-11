-- ANSI-colored pretty printing

module Text.PrettyPrint.ANSI where

open import Data.Bool
open import Data.Nat
open import Data.String hiding (parens)
import Text.PrettyPrint.Annotated as Ann
open Ann hiding (Doc; Pretty) public
open import Text.Printf
open import Function

data Color : Set where
  black red green yellow blue magenta cyan white : Color
  brightBlack brightRed brightGreen brightYellow brightBlue brightMagenta brightCyan brightWhite : Color
  rgb : ℕ → Color   -- For instance, rgb 0xffff00 for bright yellow

data ANSIColor : Set where
  fg : Color → ANSIColor
  bg : Color → ANSIColor

Doc = Ann.Doc ANSIColor

Pretty : ∀ {l} → Set l → Set l
Pretty = Ann.Pretty ANSIColor

private
  colorCode : ℕ → Color → String
  colorCode offs = λ where
      black         → basic 0
      red           → basic 1
      green         → basic 2
      yellow        → basic 3
      blue          → basic 4
      magenta       → basic 5
      cyan          → basic 6
      white         → basic 7
      brightBlack   → basic 60
      brightRed     → basic 61
      brightGreen   → basic 62
      brightYellow  → basic 63
      brightBlue    → basic 64
      brightMagenta → basic 65
      brightCyan    → basic 66
      brightWhite   → basic 67
      (rgb n)       → printf "%u;2;%u;%u;%u" (8 + offs) (n / 0x10000 % 0x100) (n / 0x100 % 0x100) (n % 0x100)
    where
      basic : ℕ → String
      basic n = printf "%u" (n + offs)

  code : ANSIColor → String
  code (fg x) = colorCode 30  x
  code (bg x) = colorCode 40 x

  reset : ANSIColor → String
  reset _ = "0"

  esc : String → String
  esc = printf "\ESC[%sm"

foreground : Color → Doc → Doc
foreground = annotate ∘ fg

background : Color → Doc → Doc
background = annotate ∘ bg

renderColor : Doc → String
renderColor = renderDecorated (esc ∘ code) (esc ∘ reset)
