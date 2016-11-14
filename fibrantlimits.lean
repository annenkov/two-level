import fibrant limit data.equiv

section pullback
universe variable u
variables A B C : Type.{max 1 u}
variable f : A → C
variable isfib : is_fibration_alt f
variable g : B → C

definition Pullback : Type :=
  Σ (a : A), Σ (b : B), Σ (c : C), (f a = c) × (g b = c)

definition Pullback' : Type := Σ (b : B), fibreₛ f (g b)

open sigma.ops
definition Pullback'_is_fibrant : is_fibration_alt
  (λ (pb : Σ (b : B), fibreₛ f (g b)), pb.1)
  := λ b, @equiv_is_fibrant _ _ (equiv.symm (fibre_projection b)) (isfib (g b))

end pullback
