import fibrant limit data.equiv algebra.category facts

open function

section pullback

universe variable u
variables {A B C : Type.{u}}
          (f : A → C) (g : B → C)
          {isfib : is_fibration_alt f}

structure Pullback (f : A → C) (g : B → C):=
  (pA : A)
  (pB : B)
  (pC : C)
  (p_law : (f pA = pC) × (g pB = pC))

definition Pullback' : Type := Σ (b : B), fibreₛ f (g b)

open sigma.ops
definition Pullback'_is_fibrant :
  is_fibration_alt (λ (pb : Pullback' f g), pb.1) :=
  λ b, @equiv_is_fibrant _ _ (equiv.symm (fibre_projection b)) (isfib (g b))

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

definition pullback_diagram (f : A → C) (g : B → C) : PullbackCat ⇒ Type_category.{u} :=
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

definition nat_transf_sigma_iso {C D : Category} {F G : C ⇒ D} :
  F ⟹ G ≃ₛ Σ (η : Π(a : C), hom (F a) (G a)), (Π{a b : C} (f : hom a b), G f ∘ η a = η b ∘ F f) :=
  equiv.mk  (λ N, match N with
                  |mk η NatSq := ⟨η, NatSq⟩
                  end)
            (λ S, match S with
                  | ⟨η, NatSq⟩ := mk η NatSq
                  end)
  begin unfold function.left_inverse, intro x, cases x, esimp end
  begin unfold function.right_inverse, unfold function.left_inverse, intro x, cases x, esimp end

open poly_unit

open equiv

definition const_funct_unit [reducible] [unfold_full] :=
  const_funct_obj PullbackCat Type_category poly_unit

definition nat_unit_Pullback_equiv :
  const_funct_unit ⟹ pullback_diagram f g ≃ₛ Pullback f g:=
  begin
    esimp,
    refine (equiv.mk _ _ _ _),
    { intro N, cases N with [η, NatSq], unfold pullback_diagram at *, esimp at *,
      refine Pullback.mk _ _ _ _,
      apply (η obA star), apply (η obB star), apply (η obC star), esimp,
      refine (_,_),
      have H : f ∘ η obA = η obC ∘ id, from NatSq (inl pb_cat_hom.f1), apply happly H,
      have H : g ∘ η obB = η obC ∘ id, from NatSq (inl pb_cat_hom.f2), apply happly H },
    { intro PB, cases PB, cases p_law with [f_eq, g_eq],
      refine mk _ _,
      intros a, unfold pullback_diagram, esimp, intro uu, cases a: esimp: assumption,
      intros a b pb, unfold pullback_diagram, cases pb with [pb_hom, p_id],
      cases pb_hom: esimp,
      { apply funext, intros, apply f_eq},
      { apply funext, intros, apply g_eq},
      { cases p_id, esimp}},
    { unfold function.left_inverse, intros x, cases x,
        esimp at *, congruence, apply funext, intros, apply funext, intro uu, esimp,
        cases x: esimp: cases uu: reflexivity },
    { unfold function.right_inverse, unfold function.left_inverse, intros x,
      cases x, cases p_law with [f_eq, g_eq], esimp }
  end

definition Pullback'_Pullback_equiv : Pullback' f g ≃ₛ Pullback f g:=
  equiv.mk
    (λ x, begin cases x with [p₁, p₂], cases p₂ with [pp₁, pp₂],
                apply Pullback.mk pp₁ p₁ (g p₁) (pp₂, rfl) end)
    (λ x, begin cases x, cases p_law with [p₁, p₂], refine ⟨ pB, #eq.ops ⟨pA, p₁ ⬝ p₂⁻¹⟩⟩end)
    (λ x, begin cases x with [p₁, p₂], cases p₂ with [pp₁, pp₂], esimp end)
    (λ x, begin cases x, cases p_law with [p₁, p₂], esimp, cases p₂, esimp end)

open eq
set_option pp.all true

open equiv poly_unit

definition poly_unit_arrow_equiv [instance] [simp] (A : Type) : (poly_unit → A) ≃ A :=
  mk (λ f, f star) (λ a, (λ u, a))
     (λ f, funext (λ x, by cases x; reflexivity))
     (λ u, rfl)

definition to_unit [reducible] [unfold_full] {C : Category} {X : C ⇒ Type_category.{u} }
  (f : Π a, poly_unit → X a) y := f y star

definition pi_unit_arrow_equiv {C : Category} {X : C ⇒ Type_category } :
  (Π a, object (const_funct_obj C Type_category poly_unit) a⟶ X a) ≃ Π y, X y :=
  begin
     esimp, refine equiv.mk to_unit (λ f y x, f y) _ (λx, rfl),
     unfold function.left_inverse, intros, apply funext, intros, apply funext, intros, cases x_2, reflexivity
  end

open eq.ops

definition nat_unit_sigma_equiv [instance] {C : Category.{1 1}} {X : C ⇒ Type_category.{u}} :
  (const_funct_obj C Type_category poly_unit ⟹ X) ≃ₛ
  Σ (c : Π y, X y), Π (y y' : C) (f : y ⟶ y'), (X f) (c y) = c y' :=
  begin
  apply equiv.trans (nat_transf_sigma_iso),
  apply @sigma_congr,

  intros ff,
  apply @pi_congr₂, intro, apply @pi_congr₂, intro b, apply @pi_congr₂, intro f',
  esimp at *, rewrite id_right,
  refine equiv.mk _ _ _ _,
  apply pi_unit_arrow_equiv,
  { intro p, apply happly p },

  { intro p, esimp at *,
   apply funext, intro x, cases x, apply p },

  { unfold function.left_inverse, intro, esimp },

  { unfold function.right_inverse, unfold function.left_inverse, intro p, esimp },
  end


end pullback
