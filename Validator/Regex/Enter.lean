import Validator.Std.Vec

import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Regex

namespace Regex

def enter (x: Regex σ): Vector σ (Symbol.num x) :=
  (Symbol.extractFrom x).2
