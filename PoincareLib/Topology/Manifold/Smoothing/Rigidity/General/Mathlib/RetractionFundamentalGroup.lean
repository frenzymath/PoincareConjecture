import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Fundamental-group injections from actual continuous retractions

Composing a mapped loop homotopy with the literal retraction
recovers the original loops after their explicit endpoint casts.
This is the product-surface injection in Waldhausen1968, pp.58--60;
see rigidity050, section2.
-/

set_option autoImplicit false

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map with an actual continuous left inverse induces
an injection at every original basepoint. Endpoint equalities are
retained explicitly. See rigidity050, section2. -/
theorem map_injective_of_leftInverse (f : C(X, Y)) (r : C(Y, X))
    (h : Function.LeftInverse r f) (x : X) :
    Function.Injective (map f x) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
  have hmaps : (a.map f.continuous).Homotopic (b.map f.continuous) :=
    Path.Homotopic.Quotient.exact hab
  have hr := (hmaps.map r).pathCast (h x).symm (h x).symm
  have ha : ((a.map f.continuous).map r.continuous).cast
      (h x).symm (h x).symm = a := by
    ext t
    exact h (a t)
  have hb : ((b.map f.continuous).map r.continuous).cast
      (h x).symm (h x).symm = b := by
    ext t
    exact h (b t)
  rw [ha, hb] at hr
  exact Path.Homotopic.Quotient.eq.mpr hr

/-- Every fixed second-coordinate product section is injective
on the original based loop classes. See rigidity050, section2. -/
theorem map_prodMk_left_injective (y : Y) (x : X) :
    Function.Injective (map
      (⟨fun z : X => (z, y), continuous_id.prodMk continuous_const⟩ : C(X, X × Y)) x) :=
  map_injective_of_leftInverse _ ⟨Prod.fst, continuous_fst⟩ (fun _ => rfl) x

/-- Every fixed first-coordinate product section is injective
on the original based loop classes. See rigidity050, section2. -/
theorem map_prodMk_right_injective (x : X) (y : Y) :
    Function.Injective (map
      (⟨fun z : Y => (x, z), continuous_const.prodMk continuous_id⟩ : C(Y, X × Y)) y) :=
  map_injective_of_leftInverse _ ⟨Prod.snd, continuous_snd⟩ (fun _ => rfl) y

end FundamentalGroup
