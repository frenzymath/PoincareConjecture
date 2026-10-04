import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.ConeTarget

/-!
# The original-parameter diameter of the target half-cone

The chart axis retains the original curve parameter. Its midpoint
diameter reconstructs exactly the affine chord of the two original
labels, even when those labels coincide. Source: Morrey ICM pp. 183-185;
M64 phase-cone normalization derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Metric
open scoped Topology

namespace PoincareMT.M64BoundaryCone

/-- A diameter on the first coordinate axis is the original parameter chord translated by
the fixed chart center. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449;
M64 derivation 2026-09-26-phase-cone-normalization.md. -/
theorem halfConeDiameter_parameter {N : ℕ} (r a b p s : ℝ) :
    halfConeDiameter r (EuclideanSpace.single (0 : Fin (N + 1)) (a - p))
      (EuclideanSpace.single 0 (b - p)) s =
      EuclideanSpace.single 0 (AffineMap.lineMap b a ((s + r) / (2 * r)) - p) := by
  simp only [halfConeDiameter, AffineMap.lineMap_apply_module]
  ext j
  by_cases hj : j = 0
  · subst j
    simp
    ring
  · simp [hj]

/-- The actual reconstruction of the affine coordinate diameter is the same
original-parameter chord used by monotone label replacement. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449; M64 derivation 2026-09-26-phase-cone-normalization.md. -/
theorem halfConeDiameter_reconstruct_parameter {N : ℕ} {M : Type*}
    {P : EuclideanSpace ℝ (Fin (N + 1)) → M} {c : ℝ → M}
    {r eta p a b : ℝ} (hr : 0 < r)
    (haxis : ∀ t ∈ Ioo (-eta) eta, P (EuclideanSpace.single 0 t) = c (t + p))
    (ha : a - p ∈ Ioo (-eta) eta) (hb : b - p ∈ Ioo (-eta) eta)
    {v : ℝ → EuclideanSpace ℝ (Fin (N + 1))}
    (h0 : v 0 = EuclideanSpace.single 0 (a - p))
    (hpi : v Real.pi = EuclideanSpace.single 0 (b - p))
    {s : ℝ} (hs : s ∈ Icc (-r) r) :
    P (halfConeDiameter r (v 0) (v Real.pi) s) =
      c (AffineMap.lineMap b a ((s + r) / (2 * r))) := by
  let t := (s + r) / (2 * r)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hs.1]) (by positivity),
      (div_le_one (by positivity : 0 < 2 * r)).mpr (by linarith [hs.2])⟩
  have heq : AffineMap.lineMap b a t - p =
      AffineMap.lineMap (b - p) (a - p) t := by
    simp only [AffineMap.lineMap_apply_module, smul_eq_mul]
    ring
  have hmem : AffineMap.lineMap b a t - p ∈ Ioo (-eta) eta := by
    rw [heq]
    exact (convex_Ioo (-eta) eta).mapsTo_lineMap hb ha ht
  rw [h0, hpi, halfConeDiameter_parameter]
  simpa only [sub_add_cancel] using haxis (AffineMap.lineMap b a t - p) hmem

end PoincareMT.M64BoundaryCone
