import Validator.Std.Memoize

import Validator.Regex.Regex
import Validator.Regex.Enter

namespace Regex

instance [Monad m] {σ: Type} [DecidableEq σ] [Hashable σ] [MonadState (MemTable enter (α := Regex σ)) m]:
  Memoize m (α := Regex σ) (β := fun r => Vector σ (symbols r)) enter where
  call r := callM enter r
