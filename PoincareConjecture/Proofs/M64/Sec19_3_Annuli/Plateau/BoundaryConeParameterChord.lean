import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeTarget













noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Metric
open scoped Topology

namespace PoincareConjecture.M64BoundaryCone




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

end PoincareConjecture.M64BoundaryCone
