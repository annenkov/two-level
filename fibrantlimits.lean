import fibrant limit


section pullback
universe variable {u}
variables A B C : Type.{max 1 u}
variable f : A → C
variable isfib : is_fibration_alt f
variable g : B → C

definition Pullback := Σ (a : A), Σ (b : B), Σ (c : C), (f a = c) × (g b = c)

definition Pullback' := Σ (b : B), fibreₛ f (g b)


open sigma.ops
definition Pullback'_is_fibrant : is_fibration_alt (λ (pb : Pullback' A B C f g), pb.1)
  :=  sorry


-- definition pullback_equiv : 

end pullback
