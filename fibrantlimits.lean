import fibrant limit data.equiv algebra.category

section pullback

universe variable u
variables {A B C : Type.{max 1 u}}
          (f : A → C) (g : B → C)
          {isfib : is_fibration_alt f}

structure Pullback (f : A → C) (g : B → C):=
  (pA : A) 
  (pB : B)
  (pC : C) 
  (p_law : (f pA = pC) × (g pB = pC))  

definition Pullback' : Type := Σ (b : B), fibreₛ f (g b)

open sigma.ops
definition Pullback'_is_fibrant : is_fibration_alt
  (λ (pb : Pullback' f g), pb.1)
  := λ b, @equiv_is_fibrant _ _ (equiv.symm (fibre_projection b)) (isfib (g b))


-- Inspired by the implementation from HoTT Lean library
inductive pb_cat_ob : Type :=
| obA : pb_cat_ob
| obB : pb_cat_ob
| obC : pb_cat_ob


open pb_cat_ob
inductive pb_cat_hom : pb_cat_ob → pb_cat_ob → Type :=
| f1 : pb_cat_hom obA obC
| f2 : pb_cat_hom obB obC

open sum

definition no_comp_pullback_hom {a b c : pb_cat_ob}
  : pb_cat_hom a b → pb_cat_hom b c → false :=
  begin intros f g, cases g: cases f end


-- Pullback as a category with three objects obA obB and obC 
-- and arrows f1 : obA → obC and f2: obB → obC
definition pullback_category : category pb_cat_ob :=
⦃ category,
  hom := λ a b, pb_cat_hom a b + (a = b),
  comp := λ a b c f g,
     begin
       cases f with [f₁, f₂]: cases g with [g₁, g₂],
       { apply inl, exfalso, apply no_comp_pullback_hom g₁ f₁},
       { apply inl, rewrite g₂, assumption},
       { apply inl, rewrite -f₂, assumption},
       { apply inr, rewrite -f₂, assumption}
     end,
  ID := λ a, inr rfl ,
  assoc := λ a b c d h g f,
    begin
    induction h with rh ph: induction g with rg pg: induction f with rf pf:
    try cases pg: try cases pf: esimp: exfalso: apply no_comp_pullback_hom; assumption; assumption
    end,
  id_left := λ a b f, begin cases f with [fl, fr], esimp, cases fr, esimp end,
  id_right := λ a b f, begin cases f with [fl, fr], esimp, cases fr, esimp end ⦄

open category

definition PullbackCat := Mk pullback_category

definition pullback_diagram (f : A → C) (g : B → C) : PullbackCat ⇒ Type_category :=
 ⦃ functor,
   object := λ c, 
     match c with
     | obA := A
     | obB := B
     | obC := C
     end,
   morphism := λ a b h,   
   begin 
    cases h with [pb_hom, p], 
    cases pb_hom, 
    apply f, apply g, cases p, apply id 
   end,
   respect_id := λ a, begin reflexivity end,
   respect_comp := 
     begin 
       intros a b c pf pg, 
       cases pf with [pb_hom_f, id_f]: 
       cases pg with [pb_hom_g, id_g]:
       try (cases pb_hom_f: cases pb_hom_g: esimp):
       try cases id_g: esimp: try cases id_f: esimp
   end ⦄

open functor natural_transformation

definition nat_unit_equiv_sigma {C : Category} {X : C ⇒ Type_category } : 
  (const_funct_obj C Type_category unit ⟹ X) ≃ₛ Σ (c : Π y : C, X y), Π (y y' : C) (f : y ⟶ y'), (X f) (c y) = c y' := sorry


end pullback
