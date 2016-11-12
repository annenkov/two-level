import algebra.category

open natural_transformation sigma.ops
open category


-- Given categories J and C, we have a canonical functor [const_funct] from the category C to the functor category C^J.
-- Here, we do not define this functor in full, but we define the object and morphism part.
-- These are called [const_funct_obj] and [const_funct_morph].
-- It would be very easy to complete this to an actual functor, but we do not need this.

definition const_funct_obj (J C : Category) (c : C) : J ⇒ C :=
  ⦃ functor,
    object := λ i, c,
    morphism := λ i j g, id,
    respect_id := λ i, eq.refl _,
    respect_comp := λi j k f g, by rewrite id_left ⦄

definition const_funct_morph (J C : Category) (c d : C) (f : c ⟶ d) : (const_funct_obj J C c) ⟹ (const_funct_obj J C d)
  := mk (λ j, f)
        begin intros, esimp, unfold const_funct_obj, rewrite id_left, rewrite id_right end


-- Given categories J and C as before, and a functor D : J ⇒ C, we have a category of cones.
-- We present it as "fibred" over C. For each object [tip : C] we have a category (here only a type) of cones
-- with "tip" [tip]. This is just the type of natural transformations between the functor constantly [tip] and D.
definition cone_with_tip [reducible] [unfold_full] {J C : Category} (D : J ⇒ C) (tip : C) := const_funct_obj _ _ tip ⟹ D

open functor
-- For [f : tip₁ ⟶ tip₂], we have a function between the type of cones with tip tip₂, and the onew with tip tip₁.
definition cone_with_tip_functorial {J C : Category} (D : J ⇒ C) (tip₁ tip₂ : C) (f : tip₁ ⟶ tip₂) (c₂ : cone_with_tip D tip₂) 
                                    : cone_with_tip D tip₁
  :=  natural_transformation.compose c₂ (const_funct_morph J C tip₁ tip₂ f)

-- A cone is a tip together with a cone under this tip.
definition cone [reducible] [unfold_full] {J C : Category} (D : J ⇒ C) := Σ c, cone_with_tip D c

-- morphisms of cones.
structure cone_hom {J C : Category} {D : J ⇒ C} (c : cone D ) (c' : cone D) : Type :=
  (chom : c.1 ⟶ c'.1)
  (commute_triangle : ∀ i, natural_map c.2 i = natural_map c'.2 i ∘ chom)

open cone_hom



definition cone_hom_eq {J C : Category} {D : J ⇒ C } {c c' : cone D}
                       {f f': cone_hom c c'} (p : chom f = chom f') : f = f' :=
  begin cases f, cases f', cases p, reflexivity end


-- Lemma stating that equality between nat. transf. is equality of morphisms (laws trivially equal)
-- Danil : It seems that the second goal (laws) is resolved automatically. So, we could use congruence
--         tactic directly to compare two natural transformations, but I'll leave this here as an example.
definition cone_with_tip_eq {J C : Category} (D : J ⇒ C) (tip : C) (c₁ c₂ : cone_with_tip D tip) :
  (natural_map c₁ = natural_map c₂) → c₁ = c₂
  := begin intros NatMapEq, cases c₁, cases c₂, congruence, esimp at *, apply NatMapEq end


definition cone_hom_comp {J C : Category} {D : J ⇒ C } {c c' c'': cone D}
                         (f' : cone_hom c' c'') (f : cone_hom c c') :=
  ⦃ cone_hom, chom := chom f' ∘ chom f,
    commute_triangle := λ i, by rewrite [assoc, -commute_triangle f', commute_triangle f] ⦄

definition cone_category [instance] [reducible] [unfold_full] {J C : Category} (D : J ⇒ C) : category (cone D) :=
  ⦃ category,
    hom := λ c c', cone_hom c c',
    comp := λ a b c f g, cone_hom_comp f g,
    ID := λi, ⦃ cone_hom, chom := id, commute_triangle := λ i, by rewrite id_right ⦄,
    assoc := λ a b c p q h g, by cases h; cases q; cases g; apply cone_hom_eq; apply assoc,
    id_left := λ a b f, cone_hom_eq (id_left (chom f)),
    id_right := λ a b f, cone_hom_eq (id_right (chom f)) ⦄

definition ConeCat [reducible] {J C : Category} (D : J ⇒ C) : Category := category.Mk (cone_category D)

set_option formatter.hide_full_terms false


-- CAVEAT: I (Nicolai) have changed this.
structure is_terminal [class] {C : Category} (c : C) := 
  (term_hom : ∀ c', hom c' c)
  (unique_term_hom : ∀ c' (f  : hom c' c), f = term_hom c')

structure has_terminal_obj [class] (C : Category) :=
  (terminal : C)
  (is_terminal_obj : is_terminal terminal)

definition limit {J C : Category} (D : J ⇒ C) : Type  := has_terminal_obj (ConeCat D)


-- binary product as a limit

open bool prod eq.ops

-- it's a bit akward to use definition of Category_two from library,
-- so we use this definition
definition cat_two : category bool :=
  ⦃ category,
    hom := λ a b, a = b,
    comp := λ a b c p q, q ⬝ p,
    ID := λ a, eq.refl _,
    assoc := λ a b c d h g f, by cases h; cases g; cases f; reflexivity,
    id_left := λ a b f, by cases f; reflexivity,
    id_right := λ a b f, by cases f; reflexivity ⦄

definition CatTwo := Mk cat_two

definition c2_functor (C : Category) (A B : C) : CatTwo ⇒ C :=
  ⦃ functor,
    object := bool.rec A B,
    morphism := (bool.rec (bool.rec (λf, id) (by contradiction))
                          (bool.rec (by contradiction) (λf, id))),
    respect_id := bool.rec rfl rfl,
    respect_comp := λi j k f g, by cases f: cases g: cases k: esimp: rewrite id_left ⦄


definition product {C : Category} (A B : C) := limit (c2_functor _ A B)

-- Type_category limits

--set_option pp.universes true

open natural_transformation
open - [notation] category

open functor unit

definition happly {A B : Type} {f g : A → B} : f = g -> ∀ x, f x = g x :=
  begin
   intros H x, rewrite H
  end

definition cone_in_pretype {J : Category.{1 1}} (D : J ⇒ Type_category) : cone D :=
⟨ cone_with_tip _ unit, -- (const_funct_obj _ _ unit) ⟹ D ,
  natural_transformation.mk
    (λ a L, natural_map L a ⋆)
    (λ a b f, funext (λ L, happly (naturality L f) _))
⟩

open function

-- just for rewriting in limit_in_pretype, because esimp gives an error
definition natural_map_proj {C D : Category} (F G: functor C D) (η :Π a, F a ⟶ G a)
  (nat : Π⦃a b : C⦄ (f : a ⟶ b), G f ∘ η a = η b ∘ F f) : natural_map (natural_transformation.mk η nat) = η := rfl

definition limit_in_pretype {J : Category.{1 1}} {D : J ⇒ Type_category} : limit D :=
  ⦃ has_terminal_obj _,
    terminal := cone_in_pretype D,
    is_terminal_obj := 
      ⦃ is_terminal _,
        term_hom := λ C, mk (λ x, cone_with_tip_functorial D unit C.1 (λ tt, x) C.2) (λ x, rfl),
        unique_term_hom := 
          begin 
            intros C f, apply cone_hom_eq, esimp, apply funext, intro x, esimp,
            -- now: need to show equality of two cones with tip unit:
            apply cone_with_tip_eq,            
            cases C.2 with [η₁, NatSq₁], esimp,
            unfold cone_with_tip_functorial, unfold natural_transformation.compose,
            -- I (Danil) have to add this stupid equalities, because unfolding is not working
            -- It seems that composition of morpshisms not resolved to composition of functions again
            have H : natural_map (const_funct_morph J Type_category unit C.1 (λ tt, x)) = (λ j, (λ tt, x)), from rfl,
            cases (chom f x) with [η₂, NatSq₂], unfold const_funct_obj at *,
            repeat rewrite natural_map_proj, rewrite H,
            apply funext, intro j, apply funext, intro u,
            -- repeat rewrite natural_map_proj, apply funext, intros j, rewrite H,
            -- apply funext, intros u,
            -- that's what rhs of the goal should simplify to
            have H' : (η₁ j ∘ λ tt, x) u = η₁ j x, from rfl,            
            exact sorry 
          end 
          -- I have changed the definition of [is_terminal], basically by saying that [hom C' C] is contractible instead of inhabited + propositional. This means that, instead of showing f = g, we have to show f = term_hom. I guess a proof of f = g would essentially combine a proof of f = term_hom with a proof of g = term_hom anyway.  
      ⦄ 
  ⦄



-- definition is_terminal_const_to_unit {C : Category} {D : C ⇒ Type_category} (C : ConeCat D) : is_terminal D :=


-- definition type_limit {C : Category} {F : C ⇒ Type_category} : limit F:=
-- ⦃ has_terminal_obj,
--   terminal := _,
--   is_terminal_obj := _
--   ⦄
