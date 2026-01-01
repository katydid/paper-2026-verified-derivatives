import Validator.Std.Vec

import Validator.Regex.Map
import Validator.Regex.Regex

namespace Regex

@[reducible, simp]
def Symbol.num: (r: Regex σ) -> Nat
  | emptyset => 0 | emptystr => 0 | symbol _ => 1 | star r1 => num r1
  | or r1 r2 => num r1 + num r2 | concat r1 r2 => num r1 + num r2

end Regex

def Vec.cast_or {r1 r2: Regex σ} (xs: Vector σ (n + Regex.Symbol.num r1 + Regex.Symbol.num r2)): Vector σ (n + Regex.Symbol.num (Regex.or r1 r2)) :=
  xs.cast_assoc

def Vec.cast_concat (xs: Vector σ (n + Regex.Symbol.num r1 + Regex.Symbol.num r2)): Vector σ (n + Regex.Symbol.num (Regex.concat r1 r2)) :=
  xs.cast_assoc
