
module Text.PrettyPrint.Annotated where

open import Agda.Builtin.FromString
open import Data.Unit
open import Data.Bool
open import Data.Maybe
open import Data.Nat as Nat hiding (_+_; _⊓_; _/_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Show as Nat
open import Data.Integer hiding (show)
open import Data.Integer.Show as Int using (show)
open import Data.Float as Float using (Float; show)
open import Data.List as List hiding (fromMaybe)
open import Data.Product
open import Data.String as String hiding (parens; braces; _<+>_)
import Data.String.Literals as String using (isString)
open import Data.Char
open import Effect.Functor
open import Effect.Monad
open import Function
open import Text.Printf

open RawFunctor ⦃ ... ⦄
open RawMonad ⦃ ... ⦄ hiding (_<$>_)

private
  _<ᵇ_ : ℤ → ℤ → Bool
  x <ᵇ y = not (y ≤ᵇ x)

  eqBool : Bool → Bool → Bool
  eqBool true  b = b
  eqBool false b = not b

  -- Returns 0 for infinities and NaN
  round! : Float → ℤ
  round! x = fromMaybe (+ 0) (Float.round x)

private variable
  ann : Set

infixl 6 _<>_ _<+>_
infixl 5 _$$_ _$+$_

data TextDetails : Set where
  Chr : Char → TextDetails
  Str : String → TextDetails

data AnnotDetails (ann : Set) : Set where
  AnnotStart : AnnotDetails ann
  NoAnnot    : TextDetails → ℤ → AnnotDetails ann
  AnnotEnd   : ann → AnnotDetails ann

data Doc (ann : Set) : Set where
  Empty      : Doc ann
  NilAbove   : Doc ann → Doc ann
  TextBeside : AnnotDetails ann → Doc ann → Doc ann
  Nest       : ℤ → Doc ann → Doc ann
  Union      : Doc ann → Doc ann → Doc ann
  NoDoc      : Doc ann
  Beside     : Doc ann → Bool → Doc ann → Doc ann
  Above      : Doc ann → Bool → Doc ann → Doc ann

{-
Here are the invariants:

1) The argument of NilAbove is never Empty. Therefore a NilAbove occupies at
least two lines.

2) The argument of @TextBeside@ is never @Nest@.

3) The layouts of the two arguments of @Union@ both flatten to the same string.

4) The arguments of @Union@ are either @TextBeside@, or @NilAbove@.

5) A @NoDoc@ may only appear on the first line of the left argument of an
   union. Therefore, the right argument of an union can never be equivalent to
   the empty set (@NoDoc@).

6) An empty document is always represented by @Empty@. It can't be hidden
   inside a @Nest@, or a @Union@ of two @Empty@s.

7) The first line of every layout in the left argument of @Union@ is longer
   than the first line of any layout in the right argument. (1) ensures that
   the left argument has a first line. In view of (3), this invariant means
   that the right argument must have at least two lines.
-}

-- RDoc is a "reduced GDoc", guaranteed not to have a top-level Above or Beside.
private
  RDoc = Doc

instance
  FunctorAnnotDetails : RawFunctor AnnotDetails
  FunctorAnnotDetails ._<$>_ f AnnotStart    = AnnotStart
  FunctorAnnotDetails ._<$>_ f (NoAnnot d i) = NoAnnot d i
  FunctorAnnotDetails ._<$>_ f (AnnotEnd a)  = AnnotEnd (f a)

  FunctorDoc : RawFunctor Doc
  FunctorDoc ._<$>_ _ Empty               = Empty
  FunctorDoc ._<$>_ f (NilAbove d)        = NilAbove (f <$> d)
  FunctorDoc ._<$>_ f (TextBeside td d)   = TextBeside (f <$> td) (f <$> d)
  FunctorDoc ._<$>_ f (Nest k d)          = Nest k (f <$> d)
  FunctorDoc ._<$>_ f (Union ur ul)       = Union (f <$> ur) (f <$> ul)
  FunctorDoc ._<$>_ _ NoDoc               = NoDoc
  FunctorDoc ._<$>_ f (Beside ld s rd)    = Beside (f <$> ld) s (f <$> rd)
  FunctorDoc ._<$>_ f (Above ud s ld)     = Above (f <$> ud) s (f <$> ld)

private
  annotSize : AnnotDetails ann → ℤ
  annotSize (NoAnnot _ l) = l
  annotSize _             = + 0

char : Char → Doc ann
char c = TextBeside (NoAnnot (Chr c) (+ 1)) Empty

-- Some text with any width. (@text s = sizedText (length s) s@)
sizedText : ℕ → String → Doc ann
sizedText l s = TextBeside (NoAnnot (Str s) (+ l)) Empty

text : String → Doc ann
text s = sizedText (String.length s) s

instance
  _ = String.isString

  IsStringDoc : IsString (Doc ann)
  IsStringDoc .IsString.Constraint _ = ⊤
  IsStringDoc .fromString s = text s

private
  indent : ℤ → String
  indent (+ n)      = String.replicate n ' '
  indent (-[1+ _ ]) = ""

-- Some text, but without any width. Use for non-printing text such as
-- a HTML or Latex tags
zeroWidthText : String → Doc ann
zeroWidthText = sizedText 0

private
  spaceText : AnnotDetails ann
  spaceText = NoAnnot (Chr ' ') (+ 1)

  nlText : AnnotDetails ann
  nlText = NoAnnot (Chr '\n') (+ 1)

empty : Doc ann
empty = Empty

isEmpty : Doc ann → Bool
isEmpty Empty = true
isEmpty _     = false

private
  above' : Doc ann → Bool → Doc ann → Doc ann
  above' p _ Empty = p
  above' Empty _ q = q
  above' p g q     = Above p g q

_$$_ : Doc ann → Doc ann → Doc ann
p $$  q = above' p false q

-- | Above, with no overlapping.
_$+$_ : Doc ann → Doc ann → Doc ann
p $+$ q = above' p true q

private
  -- mkNest checks for Nest's invariant that it doesn't have an Empty inside it
  mkNest : ℤ → Doc ann → Doc ann
  mkNest k (Nest k1 p)       = mkNest (k + k1) p
  mkNest _ NoDoc             = NoDoc
  mkNest _ Empty             = Empty
  mkNest (+ 0) p             = p
  mkNest k p                 = Nest k p

  nilAboveNest : Bool → ℤ → RDoc ann → RDoc ann
  nilAboveNest _ _ Empty = Empty
  nilAboveNest g k (Nest k1 q) = nilAboveNest g (k + k1) q
  nilAboveNest g k q =
    if not g ∧ (+ 0) <ᵇ k
    then TextBeside (NoAnnot (Str (indent k)) k) q -- No newline if no overlap
    else NilAbove (mkNest k q)                     -- Put them really above

  mutual
    maybeNilAboveNest : RDoc ann → Bool → ℤ → RDoc ann → RDoc ann
    maybeNilAboveNest Empty = nilAboveNest
    maybeNilAboveNest p     = aboveNest p

    aboveNest : RDoc ann → Bool → ℤ → RDoc ann → RDoc ann
    aboveNest NoDoc               _ _ _ = NoDoc
    aboveNest (Union p1 p2) g k q = Union (aboveNest p1 g k q)
                                          (aboveNest p2 g k q)

    aboveNest Empty               _ k q = mkNest k q
    aboveNest (Nest k1 p)         g k q = Nest k1 (aboveNest p g (k - k1) q)

    aboveNest (NilAbove p)        g k q = NilAbove (aboveNest p g k q)
    aboveNest (TextBeside s p)    g k q =
      k - annotSize s !|> λ k1 → TextBeside s (maybeNilAboveNest p g k1 q)

    aboveNest (Above _ _ _)          _ _ _ = text "ERROR: aboveNest Above"
    aboveNest (Beside _ _ _)         _ _ _ = text "ERROR: aboveNest Beside"

  beside' : Doc ann → Bool → Doc ann → Doc ann
  beside' p _ Empty = p
  beside' Empty _ q = q
  beside' p g q     = Beside p g q

_<>_ : Doc ann → Doc ann → Doc ann
p <> q = beside' p false q

_<+>_ : Doc ann → Doc ann → Doc ann
p <+> q = beside' p true  q

private
  nilBeside : Bool → RDoc ann → RDoc ann
  nilBeside _ Empty         = Empty -- Hence the text "" in the spec
  nilBeside g (Nest _ p)    = nilBeside g p
  nilBeside true p          = TextBeside spaceText p
  nilBeside false p         = p

  mutual
    {-# TERMINATING #-} -- TODO
    above : Doc ann → Bool → RDoc ann → RDoc ann
    above (Above p g1 q1)  g2 q2 = above p g1 (above q1 g2 q2)
    above p@(Beside _ _ _) g  q  = aboveNest (reduceDoc p) g (+ 0) (reduceDoc q)
    above p g q                  = aboveNest p             g (+ 0) (reduceDoc q)

    maybeNilBeside : Doc ann → Bool → RDoc ann → RDoc ann
    maybeNilBeside Empty = nilBeside
    maybeNilBeside p     = beside p

    beside : Doc ann → Bool → RDoc ann → RDoc ann
    beside NoDoc               _ _   = NoDoc
    beside (Union p1 p2)       g q   = Union (beside p1 g q) (beside p2 g q)
    beside Empty               _ q   = q
    beside (Nest k p)          g q   = Nest k $! beside p g q
    beside p@(Beside p1 g1 q1) g2 q2 =
      if eqBool g1 g2
      then beside p1 g1 $! beside q1 g2 q2
      else beside (reduceDoc p) g2 q2
    beside p@(Above _ _ _)     g q   = reduceDoc p !|> λ d → beside d g q
    beside (NilAbove p)        g q   = NilAbove $! beside p g q
    beside (TextBeside t p)    g q   = TextBeside t (maybeNilBeside p g q)

    reduceDoc : Doc ann → RDoc ann
    reduceDoc (Beside p g q) = beside p g (reduceDoc q)
    reduceDoc (Above  p g q) = above  p g (reduceDoc q)
    reduceDoc p              = p

-- Attach an annotation to a document.
annotate : ann → Doc ann → Doc ann
annotate a d = TextBeside AnnotStart
             $ beside (reduceDoc d) false
             $ TextBeside (AnnotEnd a) Empty

semi   : Doc ann
comma  : Doc ann
colon  : Doc ann
space  : Doc ann
equals : Doc ann
lparen : Doc ann
rparen : Doc ann
lbrack : Doc ann
rbrack : Doc ann
lbrace : Doc ann
rbrace : Doc ann
semi   = char ';'
comma  = char ','
colon  = char ':'
space  = char ' '
equals = char '='
lparen = char '('
rparen = char ')'
lbrack = char '['
rbrack = char ']'
lbrace = char '{'
rbrace = char '}'

nat : ℕ → Doc ann
nat n = text (Nat.show n)

int : ℤ → Doc ann
int n = text (Int.show n)

float : Float → Doc ann
float n = text (Float.show n)

parens       : Doc ann → Doc ann
brackets     : Doc ann → Doc ann
braces       : Doc ann → Doc ann
quotes       : Doc ann → Doc ann
doubleQuotes : Doc ann → Doc ann
quotes p       = char '\'' <> p <> char '\''
doubleQuotes p = char '"' <> p <> char '"'
parens p       = char '(' <> p <> char ')'
brackets p     = char '[' <> p <> char ']'
braces p       = char '{' <> p <> char '}'

maybeParens : Bool → Doc ann → Doc ann
maybeParens false = id
maybeParens true = parens

maybeBrackets : Bool → Doc ann → Doc ann
maybeBrackets false = id
maybeBrackets true = brackets

maybeBraces : Bool → Doc ann → Doc ann
maybeBraces false = id
maybeBraces true = braces

maybeQuotes : Bool → Doc ann → Doc ann
maybeQuotes false = id
maybeQuotes true = quotes

maybeDoubleQuotes : Bool → Doc ann → Doc ann
maybeDoubleQuotes false = id
maybeDoubleQuotes true = doubleQuotes

private
  data IsEmpty : Set where
    yesEmpty notEmpty : IsEmpty

  eliminateEmpty :
    (Doc ann → Bool → Doc ann → Doc ann) →
    Doc ann → Bool → IsEmpty × Doc ann → IsEmpty × Doc ann
  eliminateEmpty _    Empty _ q = q
  eliminateEmpty cons p     g q =
    notEmpty ,
    (case q of λ where
      (notEmpty , q') → cons p g q'
      (yesEmpty , _)  → p)

  reduceHoriz : Doc ann → IsEmpty × Doc ann
  reduceHoriz (Beside p g q) = eliminateEmpty Beside (reduceHoriz p .proj₂) g (reduceHoriz q)
  reduceHoriz doc            = (notEmpty , doc)

  reduceVert : Doc ann → IsEmpty × Doc ann
  reduceVert (Above  p g q) = eliminateEmpty Above (reduceVert p .proj₂) g (reduceVert q)
  reduceVert doc            = (notEmpty , doc)

hcat : List (Doc ann) → Doc ann
hcat = proj₂ ∘ reduceHoriz ∘ foldr (λ p q → Beside p false q) empty

hsep : List (Doc ann) → Doc ann
hsep = proj₂ ∘ reduceHoriz ∘ foldr (λ p q → Beside p true q)  empty

vcat : List (Doc ann) → Doc ann
vcat = proj₂ ∘ reduceVert ∘ foldr (λ p q → Above p false q) empty

nest : ℕ → Doc ann → Doc ann
nest k p = mkNest (+ k) (reduceDoc p)

punctuate : Doc ann → List (Doc ann) → List (Doc ann)
punctuate _ [] = []
punctuate {ann} p (x ∷ xs) = go x xs
  where go : Doc ann → List (Doc ann) → List (Doc ann)
        go y []       = [ y ]
        go y (z ∷ zs) = (y <> p) ∷ go z zs

private
  mkUnion : Doc ann → Doc ann → Doc ann
  mkUnion Empty _ = Empty
  mkUnion p q     = Union p q

  oneLiner : Doc ann → Doc ann
  oneLiner NoDoc               = NoDoc
  oneLiner Empty               = Empty
  oneLiner (NilAbove _)        = NoDoc
  oneLiner (TextBeside s p)    = TextBeside s (oneLiner p)
  oneLiner (Nest k p)          = Nest k (oneLiner p)
  oneLiner (Union p _)         = oneLiner p
  oneLiner (Above _ _ _)       = NoDoc -- text "Error: oneLiner Above"
  oneLiner (Beside _ _ _)      = NoDoc -- text "Error: oneLiner Beside"

private
  mutual
    sep1 : Bool → RDoc ann → ℤ → List (Doc ann) → RDoc ann
    sep1 _ NoDoc               _ _  = NoDoc
    sep1 g (Union p q)         k ys = Union (sep1 g p k ys)
                                      $ aboveNest q false k (reduceDoc (vcat ys))

    sep1 g Empty               k ys = mkNest k (sepX g ys)
    sep1 g (Nest n p)          k ys = Nest n (sep1 g p (k - n) ys)

    sep1 _ (NilAbove p)        k ys = NilAbove
                                      (aboveNest p false k (reduceDoc (vcat ys)))
    sep1 g (TextBeside s p) k ys    = TextBeside s (sepNB g p (k - annotSize s) ys)
    sep1 _ (Above _ _ _)          _ _  = text "Error: sep1 Above"
    sep1 _ (Beside _ _ _)         _ _  = text "Error: sep1 Beside"

    sepX : Bool → List (Doc ann) → Doc ann
    sepX _ []       = empty
    sepX x (p ∷ ps) = sep1 x (reduceDoc p) (+ 0) ps

    sepNB : Bool → Doc ann → ℤ → List (Doc ann) → Doc ann
    sepNB g (Nest _ p) k ys = sepNB g p k ys
    sepNB g Empty k ys =
      let rest = if g then hsep ys else hcat ys in
      mkUnion (oneLiner (nilBeside g (reduceDoc rest)))
              (nilAboveNest false k (reduceDoc (vcat ys)))
    sepNB g p k ys = sep1 g p k ys

sep  : List (Doc ann) → Doc ann
sep = sepX true

cat : List (Doc ann) → Doc ann
cat = sepX false

hang : Doc ann → ℕ → Doc ann → Doc ann
hang d1 n d2 = sep (d1 ∷ nest n d2 ∷ [])

---------------------------------------------------------------------------
-- Filling

private
  elideNest : Doc ann → Doc ann
  elideNest (Nest _ d) = d
  elideNest d          = d

  mutual
    {-# TERMINATING #-}
    fill1 : Bool → RDoc ann → ℤ → List (Doc ann) → Doc ann
    fill1 _ NoDoc               _ _  = NoDoc
    fill1 g (Union p q)         k ys = Union (fill1 g p k ys)
                                            (aboveNest q false k (fill g ys))
    fill1 g Empty               k ys = mkNest k (fill g ys)
    fill1 g (Nest n p)          k ys = Nest n (fill1 g p (k - n) ys)
    fill1 g (NilAbove p)        k ys = NilAbove (aboveNest p false k (fill g ys))
    fill1 g (TextBeside s p)    k ys = TextBeside s (fillNB g p (k - annotSize s) ys)
    fill1 _ (Above _ _ _)       _ _  = text "Error: fill1 Above"
    fill1 _ (Beside _ _ _)      _ _  = text "Error: fill1 Beside"

    fillNB : Bool → Doc ann → ℤ → List (Doc ann) → Doc ann
    fillNB g (Nest _ p)  k ys     = fillNB g p k ys
    fillNB _ Empty _ []           = Empty
    fillNB g Empty k (Empty ∷ ys) = fillNB g Empty k ys
    fillNB g Empty k (y ∷ ys)     = fillNBE g k y ys
    fillNB g p k ys               = fill1 g p k ys


    fillNBE : Bool → ℤ → Doc ann → List (Doc ann) → Doc ann
    fillNBE g k y ys
      = mkUnion (nilBeside g (fill1 g ((elideNest ∘ oneLiner ∘ reduceDoc) y) k' ys))
                (nilAboveNest false k (fill g (y ∷ ys)))
      where k' = if g then k - + 1 else k

    fill : Bool → List (Doc ann) → RDoc ann
    fill _ []       = empty
    fill g (p ∷ ps) = fill1 g (reduceDoc p) (+ 0) ps

fcat : List (Doc ann) → Doc ann
fcat = fill false

fsep : List (Doc ann) → Doc ann
fsep = fill true


---------------------------------------------------------------------------
-- Rendering

private
  fits : ℤ → Doc ann → Bool -- true if *first line* of Doc fits in space available
  fits {ann} n p = (+ 0 ≤ᵇ n) ∧ go p
    where
      go : Doc ann → Bool
      go NoDoc            = false
      go Empty            = true
      go (NilAbove _)     = true
      go (TextBeside s p) = fits (n - annotSize s) p
      go (Above _ _ _)    = false -- text "Error: fits Above"
      go (Beside _ _ _)   = false -- text "Error: fits Beside"
      go (Union _ _)      = false -- text "Error: fits Union"
      go (Nest _ _)       = false -- text "Error: fits Nest"

  nicest1 : ℤ → ℤ → ℤ → Doc ann → Doc ann → Doc ann
  nicest1 w r sl p q = if fits ((w ⊓ r) - sl) p then p else q

  nicest : ℤ → ℤ → Doc ann → Doc ann → Doc ann
  nicest w r = nicest1 w r (+ 0)

  best : ℤ   -- Line length.
       → ℤ   -- Ribbon length.
       → RDoc ann
       → RDoc ann  -- No unions in here!
  best {ann} w0 r = get w0
    where
      mutual
        get : ℤ → Doc ann → Doc ann
        get _ Empty               = Empty
        get _ NoDoc               = NoDoc
        get w (NilAbove p)        = NilAbove (get w p)
        get w (TextBeside s p)    = TextBeside s (get1 w (annotSize s) p)
        get w (Nest k p)          = Nest k (get (w - k) p)
        get w (Union p q)         = nicest w r (get w p) (get w q)
        get _ (Above _ _ _)       = text "Error: best get Above"
        get _ (Beside _ _ _)      = text "Error: best get Beside"

        get1 : ℤ → ℤ → Doc ann → Doc ann
        get1 _ _  Empty               = Empty
        get1 _ _  NoDoc               = NoDoc
        get1 w sl (NilAbove p)        = NilAbove (get (w - sl) p)
        get1 w sl (TextBeside s p)    = TextBeside s (get1 w (sl + annotSize s) p)
        get1 w sl (Nest _ p)          = get1 w sl p
        get1 w sl (Union p q)         = nicest1 w r sl (get1 w sl p)
                                                      (get1 w sl q)
        get1 _ _  (Above _ _ _)       = text "Error: best get1 Above"
        get1 _ _  (Beside _ _ _)      = text "Error: best get1 Beside"

  nonEmptySet : Doc ann → Bool
  nonEmptySet NoDoc            = false
  nonEmptySet (Union _ _)      = true
  nonEmptySet Empty            = true
  nonEmptySet (NilAbove _)     = true
  nonEmptySet (TextBeside _ p) = nonEmptySet p
  nonEmptySet (Nest _ p)       = nonEmptySet p
  nonEmptySet (Above _ _ _)    = false  -- error
  nonEmptySet (Beside _ _ _)   = false  -- error

data Mode : Set where
  PageMode    : Mode -- Normal rendering ('lineLength' and 'ribbonsPerLine' respected).
  LeftMode    : Mode -- No indentation, infinitely long lines ('lineLength' ignored),
                     -- but explicit new lines, i.e., `text "one" $$ text "two"`, are
                     -- respected.
  OneLineMode : Mode -- All on one line, 'lineLength' ignored and explicit new lines
                     -- `$$` are turned into spaces.

-- -- | A rendering style. Allows us to specify constraints to choose among the
-- -- many different rendering options.
record Style : Set where
  field
    mode           : Mode
    lineLength     : ℕ
    ribbonsPerLine : Float

open Style

style : Style
style = record { lineLength = 100; ribbonsPerLine = 1.5; mode = PageMode }

private
  txtPrinter : TextDetails → String → String
  txtPrinter (Chr c)   s  = String.fromList [ c ] String.++ s
  txtPrinter (Str s1)  s2 = s1 String.++ s2

  module _ {A : Set} (txt : AnnotDetails ann → A → A) (end : A) where

    easyDisplay : AnnotDetails ann
                → (Doc ann → Doc ann → Bool)
                → Doc ann
                → A
    easyDisplay nlSpaceText chooseFirst = lay
      where
        lay : Doc ann → A
        lay NoDoc            = end -- error
        lay (Union p q)      = if chooseFirst p q then lay p else lay q
        lay (Nest _ p)       = lay p
        lay Empty            = end
        lay (NilAbove p)     = txt nlSpaceText (lay p)
        lay (TextBeside s p) = txt s (lay p)
        lay (Above _ _ _)    = end -- error
        lay (Beside _ _ _)   = end -- error

    display : Mode → ℤ → ℤ → Doc ann → A
    display m pageWidth ribbonWidth =
      case pageWidth - ribbonWidth of λ
        gapWidth → display' gapWidth (gapWidth /ℕ 2)
      where
        display' : ℤ → ℤ → Doc ann → A
        display' gapWidth shift = lay (+ 0)
          where
            mutual
              lay : ℤ → Doc ann → A
              lay k (Nest k1 p)  = lay (k + k1) p
              lay _ Empty        = end
              lay k (NilAbove p) = txt nlText (lay k p)
              lay k (TextBeside s p) = lay1 k s p

              lay _ (Above _ _ _)  = end -- error
              lay _ (Beside _ _ _) = end -- error
              lay _ NoDoc          = end -- error
              lay _ (Union _ _)    = end -- error

              lay1 : ℤ → AnnotDetails ann → Doc ann → A
              lay1 k s p = let r = k + annotSize s
                          in txt (NoAnnot (Str (indent k)) k) $ txt s $ lay2 r p

              lay2 : ℤ → Doc ann → A
              lay2 k (NilAbove p)     = txt nlText $ lay k p
              lay2 k (TextBeside s p) = txt s $ lay2 (k + annotSize s) p
              lay2 k (Nest _ p)       = lay2 k p
              lay2 _ Empty            = end
              lay2 _ (Above _ _ _)    = end -- error
              lay2 _ (Beside _ _ _)   = end -- error
              lay2 _ NoDoc            = end -- error
              lay2 _ (Union _ _)      = end -- error

    fullRenderAnn : Mode    -- ^ Rendering mode.
                  → ℤ       -- ^ Line length.
                  → Float   -- ^ Ribbons per line.
                  → Doc ann -- ^ The document.
                  → A       -- ^ Result.
    fullRenderAnn OneLineMode _ _ doc
      = easyDisplay spaceText (λ _ _ → false) (reduceDoc doc)
    fullRenderAnn LeftMode    _ _ doc
      = easyDisplay nlText (λ p _ → nonEmptySet p) (reduceDoc doc)
    fullRenderAnn m lineLen ribbons doc
      = display m lineLen ribbonLen doc'
      where
        ribbonLen : ℤ
        ribbonLen = round! (Float.fromℤ lineLen Float.÷ ribbons)
        doc' = best lineLen ribbonLen (reduceDoc doc)


  fullRender : {A : Set}
            → Mode                  -- ^ Rendering mode.
            → ℤ                     -- ^ Line length.
            → Float                 -- ^ Ribbons per line.
            → (TextDetails → A → A) -- ^ What to do with text.
            → A                     -- ^ What to do at the end.
            → Doc ann               -- ^ The document.
            → A                     -- ^ Result.
  fullRender {ann = ann} {A} m l r txt end = fullRenderAnn annTxt end m l r
    where
    annTxt : AnnotDetails ann → A → A
    annTxt (NoAnnot s _) = txt s
    annTxt _             = id

render : Doc ann → String
render = fullRender (mode style) (+ lineLength style) (ribbonsPerLine style)
                    txtPrinter ""

renderStyle : Style → Doc ann → String
renderStyle s = fullRender (mode s) (+ lineLength s) (ribbonsPerLine s)
                txtPrinter ""

-- Rendering Annotations -------------------------------------------------------

private
  record Span ann : Set where
    constructor mkSpan
    field
      spanStart      : ℤ
      spanLength     : ℤ
      spanAnnotation : ann

  open Span

  record Spans ann : Set where
    constructor mkSpans
    field
      sOffset : ℤ
      sStack  : List (ℤ → Span ann)
      sSpans  : List (Span ann)
      sOutput : String

  open Spans

  renderSpans : Doc ann → String × List (Span ann)
  renderSpans {ann} =
    finalize
    ∘ fullRenderAnn spanPrinter emptySpans
                    (mode style) (+ lineLength style) (ribbonsPerLine style)
    where

    emptySpans : Spans ann
    emptySpans = record { sOffset = + 0; sStack = []; sSpans = []; sOutput = "" }

    finalize : Spans ann → String × List (Span ann)
    finalize (mkSpans size _ spans out) = (out , List.map adjust spans)
      where
      adjust : Span ann → Span ann
      adjust s = record s { spanStart = size - spanStart s }

    makeSpan : ann → ℤ → ℤ → Span ann
    makeSpan a end start = record { spanStart      = start
                                  ; spanLength     = start - end
                                  ; spanAnnotation = a }

    -- the document gets generated in reverse, which is why the starting
    -- annotation ends the annotation.
    spanPrinter : AnnotDetails ann → Spans ann → Spans ann
    spanPrinter AnnotStart s =
      case sStack s of λ where
        (sp ∷ rest) → record s { sSpans = sp (sOffset s) ∷ sSpans s; sStack = rest }
        _           → s -- error

    spanPrinter (AnnotEnd a) s =
      record s { sStack = makeSpan a (sOffset s) ∷ sStack s }

    spanPrinter (NoAnnot td l) s =
      case td of λ where
        (Chr  c) → record s { sOutput = fromChar c String.++ sOutput s; sOffset = sOffset s + l }
        (Str  t) → record s { sOutput = t String.++ sOutput s; sOffset = sOffset s + l }

renderDecorated : (ann → String) -- ^ Starting an annotation.
                → (ann → String) -- ^ Ending an annotation.
                → Doc ann → String
renderDecorated {ann} startAnn endAnn =
  proj₁ ∘ fullRenderAnn annPrinter ("" , [])
                        (mode style) (+ lineLength style) (ribbonsPerLine style)
  where
    annPrinter : AnnotDetails ann → String × List ann → String × List ann
    annPrinter AnnotStart    (rest , [])     = (rest , []) -- error
    annPrinter AnnotStart    (rest , a ∷ as) = startAnn a String.++ rest , as
    annPrinter (AnnotEnd a)  (rest , stack)  = endAnn a String.++ rest , a ∷ stack
    annPrinter (NoAnnot s _) (rest , stack)  = txtPrinter s rest , stack

renderDecoratedM : {M : Set → Set} {R : Set}
                 → ⦃ RawMonad M ⦄
                 → (ann    → M R) -- ^ Starting an annotation.
                 → (ann    → M R) -- ^ Ending an annotation.
                 → (String → M R) -- ^ Text formatting.
                 → M R            -- ^ Document end.
                 → Doc ann → M R
renderDecoratedM {ann} {M} {R} startAnn endAnn txt docEnd =
  proj₁ ∘ fullRenderAnn annPrinter (docEnd , [])
                        (mode style) (+ lineLength style) (ribbonsPerLine style)
  where
    annPrinter : AnnotDetails ann → M R × List ann → M R × List ann
    annPrinter AnnotStart          (rest , [])     = rest                       , [] -- error
    annPrinter AnnotStart          (rest , a ∷ as) = (startAnn a >> rest)       , as
    annPrinter (AnnotEnd a)        (rest , stack)  = (endAnn a >> rest)         , a ∷ stack
    annPrinter (NoAnnot (Chr c) _) (rest , stack)  = (txt (fromChar c) >> rest) , stack
    annPrinter (NoAnnot (Str s) _) (rest , stack)  = (txt s >> rest)            , stack
