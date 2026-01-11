import Validator.Std.Hashable
import Validator.Std.Memoize

import Validator.Regex.Regex
import Validator.Regex.Leave

namespace Regex

def leave2 {σ: Type}: (Σ (r: Regex σ), (Vector Bool (symbols r))) → Regex σ
  | ⟨r, bools⟩ => leave r bools

instance [Monad m] {σ: Type} [DecidableEq σ] [Hashable σ] [MonadState (MemTable leave2 (α := (Σ (r: Regex σ), (Vector Bool (symbols r))))) m]:
  Memoize m (α := (Σ (r: Regex σ), (Vector Bool (symbols r)))) (β := fun _ => Regex σ) leave2 where
  call r := callM leave2 r
