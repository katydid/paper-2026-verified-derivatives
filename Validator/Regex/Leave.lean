import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.Replace

namespace Regex

def leave
  (r: Regex σ)
  (ps: Vector Bool (Symbol.num r))
  : Regex σ :=
  let points: Vector (σ × Bool) (Symbol.num r) := Vec.zip (Symbol.extractFrom r).2 ps
  let replaced: Regex (σ × Bool) := Symbol.replaceFrom (Symbol.extractFrom r).1 points
  Regex.Point.derive replaced
