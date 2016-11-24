import fibrant matching inverse algebra.category limit data.fin

open invcat category functor matching_object Fib

definition fib_category : category Fib :=
  ⦃ category, 
    hom := λ a b, pretype a → pretype b,
    comp := λ a b c, function.comp ,
    ID := _,
    assoc := λ a b c d h g f, eq.symm (function.comp.assoc h g f),
    id_left := λ a b f,  function.comp.left_id f,
    id_right := λ a b f, function.comp.right_id f ⦄

definition FibCat := Mk fib_category 

definition is_finite [class] (C : Category) := Σ n, C ≃ₛ fin n

open equiv equiv.ops

section reedy
  universe variable u
  variables {C : Category.{1 1}}

  definition is_reedy_fibrant (X : C ⇒ Type_category.{max 1 u}) [invcat C] := Π z,
    is_fibration_alt (matching_obj_map.{u} X z)

  definition fibrant_limit [invC : invcat C] [finC : is_finite C] (X : C ⇒ Type_category.{max 1 u}) (rfib : is_reedy_fibrant.{u} X) : 
    is_fibrant (limit_obj (limit_in_pretype.{u} X)) := 
    begin
      cases finC with [n, equiv], 
      induction n with [n'],
      { apply sorry },
      { esimp, cases invC,
        apply sorry }
    end
end reedy
