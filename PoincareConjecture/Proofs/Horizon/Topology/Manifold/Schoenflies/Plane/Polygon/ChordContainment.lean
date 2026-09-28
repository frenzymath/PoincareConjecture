import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor










set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Plane




theorem exists_uniform_short_chord_mem_open
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set X} (hK : IsCompact K) {c : X → ℝ → E} {l u : ℝ}
    (hc : ContinuousOn (fun p : X × ℝ => c p.1 p.2) (K ×ˢ Icc l u))
    {U : Set (X × E)} (hU : IsOpen U)
    (hcurve : ∀ z ∈ K, ∀ s ∈ Icc l u, (z, c z s) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ a ∈ Icc l u, ∀ b ∈ Icc l u,
      |b - a| < δ → ∀ t ∈ Icc (0 : ℝ) 1,
        (z, AffineMap.lineMap (c z a) (c z b) t) ∈ U := by
  let F : X × ℝ → X × E := fun p => (p.1, c p.1 p.2)
  have hF : ContinuousOn F (K ×ˢ Icc l u) := continuousOn_fst.prodMk hc
  have hcompact : IsCompact (F '' (K ×ˢ Icc l u)) :=
    (hK.prod isCompact_Icc).image_of_continuousOn hF
  have hsub : F '' (K ×ˢ Icc l u) ⊆ U := by
    rintro y ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
    exact hcurve z hz s hs
  obtain ⟨ρ, hρ, hthick⟩ := hcompact.exists_thickening_subset_open hU hsub
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hc) ρ hρ
  refine ⟨δ, hδ, ?_⟩
  intro z hz a ha b hb hmesh t ht
  have hend : dist (c z a) (c z b) < ρ := hclose (z, a) ⟨hz, ha⟩ (z, b) ⟨hz, hb⟩ (by
    simpa only [dist_prod_same_left, Real.dist_eq, abs_sub_comm] using hmesh)
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(z, c z a), ⟨(z, a), ⟨hz, ha⟩, rfl⟩, ?_⟩
  rw [dist_prod_same_left, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left dist_nonneg ht.2).trans_lt hend

end Poincare.Manifold.Schoenflies.Plane
