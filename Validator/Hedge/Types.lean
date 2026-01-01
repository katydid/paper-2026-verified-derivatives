import Validator.Regex.Regex

-- ## Definition 3.2.3: Regular Hedge Grammar
--   𝐺 = (𝑁, 𝑇, 𝑆, 𝑃)
--   𝑁 a finite set of non-terminals
--   𝑇 a finite set of terminals
--   𝑆 the start symbol of a regular hedge grammar is a regular expression comprising pairs of nonterminals and terminals (a regular expression over N × T)
--   𝑃 a set of production rules of a regular hedge grammar are of the form X → r such that r is a regular expression over N × T.

namespace Hedge

-- Ref is a non-terminal, where n represents the number of non-terminals
abbrev Grammar.Ref (n: Nat) := Fin n

abbrev Grammar.Symbol (n: Nat) (φ: Type) := (φ × Ref n)

abbrev Grammar.Rule (n: Nat) (φ: Type) := Regex (Symbol n φ)

structure Grammar (n: Nat) (φ: Type) where
  start: Grammar.Rule n φ
  prods: Vector (Grammar.Rule n φ) n

end Hedge

namespace Hedge.Grammar

abbrev Symbols n φ l := Vector (Symbol n φ) l

def hashVector [Hashable α] (xs: Vector α n): UInt64 :=
  hash xs.toList

instance (α: Type) (n: Nat) [Hashable α] : Hashable (Vector α n) where
  hash := hashVector
