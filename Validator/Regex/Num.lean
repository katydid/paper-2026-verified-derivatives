import Validator.Std.Vec

import Validator.Regex.Map
import Validator.Regex.Regex

namespace Regex

@[reducible, simp]
def symbols: (r: Regex σ) → Nat
  | emptyset => 0 | emptystr => 0 | symbol _ => 1 | star r1 => symbols r1
  | or r1 r2 => symbols r1 + symbols r2 | concat r1 r2 => symbols r1 + symbols r2

end Regex

def Vec.cast_or {r1 r2: Regex σ} (xs: Vector σ (n + Regex.symbols r1 + Regex.symbols r2)): Vector σ (n + Regex.symbols (Regex.or r1 r2)) :=
  xs.cast_assoc

def Vec.cast_concat (xs: Vector σ (n + Regex.symbols r1 + Regex.symbols r2)): Vector σ (n + Regex.symbols (Regex.concat r1 r2)) :=
  xs.cast_assoc
