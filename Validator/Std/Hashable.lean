instance {α: Type} {β: α -> Type} [Hashable α] [∀ a, Hashable (β a)] : Hashable (Σ (a: α), β a) where
  hash | ⟨a, b⟩ => mixHash (hash a) (hash b)

instance [Hashable α] : Hashable (Vector α n) where
  hash | ⟨a, _⟩ => (hash a)
