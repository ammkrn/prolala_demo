import Lake
open Lake DSL

package Prolala {
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "089ae0a61756a84e383111da1f6697210456ed3a"
  }]
}
