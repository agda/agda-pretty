More or less complete Agda port of the [pretty](https://hackage.haskell.org/package/pretty) Haskell package.

Modules
- [`Text.PrettyPrint.Annotated`](src/Text/PrettyPrint/Annotated.agda) (the actual code)
- [`Text.PrettyPrint`](src/Text/PrettyPrint.agda) (thin wrapper setting annotations to ⊤)
- [`Text.PrettyPrint.ANSI`](src/Text/PrettyPrint/ANSI.agda) (ANSI-color annotations, _not in the Haskell package_)
