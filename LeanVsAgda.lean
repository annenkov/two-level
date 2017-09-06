-- A self-contained example which fails to work in Agda due to the difference in
-- type class instances resolution mechanism

constant is_fibrant' : Type → Prop

structure is_fibrant [class] (X : Type) := mk ::
fib_internal : is_fibrant' X

constant pi_is_fibrant' {X : Type} {Y : X → Type}
  : is_fibrant X → (Π (x : X), is_fibrant (Y x)) → is_fibrant' (Π (x : X), Y x)

definition pi_is_fibrant [instance] {X : Type}{Y : X → Type}
           [fibX : is_fibrant X] [fibY : Π (x : X), is_fibrant (Y x)]
  : is_fibrant (Π (x : X), Y x) := is_fibrant.mk (pi_is_fibrant' fibX fibY)

constant fib_eq {X : Type} [is_fibrant X] : X → X → Type

notation x ~ y := fib_eq x y

constant refl {X : Type}[is_fibrant X](x : X) : x ~ x

definition pi_eq {A : Type} [fibA : is_fibrant A]
                 {Q : A → Type} [fibB : Π a, is_fibrant (Q a)]
  : Π (f : Π (a :A), Q a), f ~ f := λ x, refl _


set_option pp.implicit true
set_option pp.notation false

check @pi_eq
