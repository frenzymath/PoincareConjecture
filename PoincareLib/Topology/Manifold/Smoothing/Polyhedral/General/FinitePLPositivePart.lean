import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine

/-!
# Positive parts of finite PL functions

Align the zero hyperplanes of all affine formulas. On every new
simplex the positive part is either the same formula or zero.
This preserves the sign needed in Alexander's collar deformation,
pp. 7--8; see M76 derivation 154.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positive part of a finite piecewise-affine scalar
function is finite piecewise-affine on its original exact domain.
See Hudson pp. 12--17 and M76 derivation 154. -/
theorem FinitePiecewiseAffineOn.positivePart {f : E → ℝ} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) :
    FinitePiecewiseAffineOn (fun x => max 0 (f x)) S := by
  classical
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  let : Fintype K.faces := hK.fintype
  choose A hA using fun s : K.faces => hfaces s.val s.property
  let H : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.image fun s : K.faces => (A s).toAffineMap
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, _, hLH⟩ := K.exists_subdivision_respectsAffineHyperplanes hK hN H
  refine ⟨L, hL, hLK.space_eq, fun s hs => ?_⟩
  obtain ⟨t, ht, hst⟩ := hLK.face_subset s hs
  let i : K.faces := ⟨t, ht⟩
  have hmem : (A i).toAffineMap ∈ H := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rcases hLH _ hmem s hs with hnonpos | hnonneg
  · refine ⟨ContinuousAffineMap.const ℝ E (0 : ℝ), fun x hx => ?_⟩
    change max 0 (f x) = 0
    rw [hA i (hst hx)]
    exact max_eq_left (hnonpos x hx)
  · refine ⟨A i, fun x hx => ?_⟩
    change max 0 (f x) = A i x
    rw [hA i (hst hx)]
    exact max_eq_right (hnonneg x hx)

end Geometry
