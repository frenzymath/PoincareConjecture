import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Reparametrization









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


theorem normalize_smul_pos (g : RiemannianMetric 2 S) (x : S)
    (v : TangentSpace (𝓡 2) x) {c : ℝ} (hc : 0 < c) :
    (Real.sqrt (g.inner x (c • v) (c • v)))⁻¹ • (c • v) =
      (Real.sqrt (g.inner x v v))⁻¹ • v := by
  have hinner : g.inner x (c • v) (c • v) = c ^ 2 * g.inner x v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hinner, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  simp [smul_smul, mul_inv_rev, hc.ne']


theorem normalize_smul_neg (g : RiemannianMetric 2 S) (x : S)
    (v : TangentSpace (𝓡 2) x) {c : ℝ} (hc : c < 0) :
    (Real.sqrt (g.inner x (c • v) (c • v)))⁻¹ • (c • v) =
      -((Real.sqrt (g.inner x v v))⁻¹ • v) := by
  have h := g.normalize_smul_pos x (-v) (neg_pos.mpr hc)
  simpa only [neg_smul, smul_neg, neg_neg, map_neg, neg_apply] using h

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}




theorem normalized_fields_eventuallyEq_or_neg_along_reparam
    {T W V Z : (x : S) → TangentSpace (𝓡 2) x}
    {γ : ℝ → S} {φ φ' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hφ : ∀ s ∈ I, HasDerivAt φ (φ' s) s) (hφ' : ContinuousOn φ' I)
    (hγ : ∀ s ∈ I, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ (φ s))
    (hV : ∀ s ∈ I, V (γ (φ s)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ s) 1)
    (hZ : ∀ s ∈ I, Z (γ (φ s)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) s 1)
    (hregular : ∀ s ∈ I, Z (γ (φ s)) ≠ 0)
    (hT : ∀ s ∈ I, T (γ (φ s)) =
      (Real.sqrt (g.inner (γ (φ s)) (V (γ (φ s))) (V (γ (φ s)))))⁻¹ • V (γ (φ s)))
    (hW : ∀ s ∈ I, W (γ (φ s)) =
      (Real.sqrt (g.inner (γ (φ s)) (Z (γ (φ s))) (Z (γ (φ s)))))⁻¹ • Z (γ (φ s)))
    {t : ℝ} (ht : t ∈ I) :
    (∀ᶠ s in 𝓝 t, W (γ (φ s)) = T (γ (φ s))) ∨
      (∀ᶠ s in 𝓝 t, W (γ (φ s)) = -T (γ (φ s))) := by
  have hscale (s : ℝ) (hs : s ∈ I) : Z (γ (φ s)) = φ' s • V (γ (φ s)) := by
    rw [hZ s hs, mfderiv_curve_reparam (hγ s hs) (hφ s hs), hV s hs]
  have hnz : φ' t ≠ 0 := by
    intro hzero
    apply hregular t ht
    rw [hscale t ht, hzero, zero_smul]
  have hcont := hφ'.continuousAt (hI.mem_nhds ht)
  rcases lt_or_gt_of_ne hnz with hneg | hpos
  · right
    have hsign : ∀ᶠ s in 𝓝 t, φ' s < 0 := hcont.eventually (gt_mem_nhds hneg)
    filter_upwards [hI.mem_nhds ht, hsign] with s hs hsign
    rw [hW s hs, hT s hs, hscale s hs]
    exact g.normalize_smul_neg _ _ hsign
  · left
    have hsign : ∀ᶠ s in 𝓝 t, 0 < φ' s := hcont.eventually (lt_mem_nhds hpos)
    filter_upwards [hI.mem_nhds ht, hsign] with s hs hsign
    rw [hW s hs, hT s hs, hscale s hs]
    exact g.normalize_smul_pos _ _ hsign

end PoincareConjecture.LeviCivitaData
