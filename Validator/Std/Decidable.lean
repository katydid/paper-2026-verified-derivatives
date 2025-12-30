
@[inline_if_reduce, nospecialize] def decideRel (p : α -> β -> Prop) [DecidableRel p] : α -> β -> Bool :=
  fun a b => p a b
