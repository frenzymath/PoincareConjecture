import PoincareConjecture.Proofs.M76.Mathlib.ConvexLinearInjectivity

set_option autoImplicit false

open Set

namespace AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]

theorem injOn_affineSpan_of_injOn_convex (a : E →ᵃ[ℝ] F) {C : Set E}
    (hC : Convex ℝ C) (hne : C.Nonempty) (ha : InjOn a C) :
    InjOn a (affineSpan ℝ C) := by
  have heq (x y : E) : a x = a y ↔ a.linear x = a.linear y := by
    have hd (z : E) : a z = a.linear z + a 0 := congrFun a.decomp z
    rw [hd x, hd y, add_right_cancel_iff]
  have hl : InjOn a.linear C := fun x hx y hy h => ha hx hy ((heq x y).mpr h)
  have hspan := a.linear.injOn_affineSpan_of_injOn_convex hC hne hl
  exact fun x hx y hy h => hspan hx hy ((heq x y).mp h)

theorem affineIndependent_comp_of_injOn_convexHull {ι : Type*} (a : E →ᵃ[ℝ] F)
    {p : ι → E} (hp : AffineIndependent ℝ p)
    (ha : InjOn a (convexHull ℝ (range p))) : AffineIndependent ℝ (a ∘ p) := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact affineIndependent_of_subsingleton ℝ _
  | inr h =>
    have hspan := a.injOn_affineSpan_of_injOn_convex (convex_convexHull ℝ _)
      (range_nonempty p).convexHull ha
    rw [affineSpan_convexHull] at hspan
    exact hp.map_of_injOn_affineSpan a hspan

end AffineMap
