import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Horoball














set_option autoImplicit false

open Set Metric

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

theorem exists_maximal_innerParallelSet {K F : Set M} (hK : IsCompact K)
    {x : M} (hx : x ∈ K) (hdepth : 0 < infDist x F) :
    ∃ R : ℝ, 0 < R ∧ {y ∈ K | R ≤ infDist y F}.Nonempty ∧
      IsCompact {y ∈ K | R ≤ infDist y F} ∧
      (∀ y ∈ K, infDist y F ≤ R) ∧
      ∀ s : ℝ, R < s → {y ∈ K | s ≤ infDist y F} = ∅ := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩
    (continuous_infDist_pt F).continuousOn
  refine ⟨infDist z F, hdepth.trans_le (hmax hx), ⟨z, hz, le_rfl⟩, ?_,
    fun y hy => hmax hy, ?_⟩
  · exact hK.inter_right (isClosed_Ici.preimage (continuous_infDist_pt F))
  · intro s hs
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact (not_le_of_gt hs) (hy.2.trans (hmax hy.1))

theorem interior_maximal_innerParallelSet_eq_empty (hseg : HasMinimizingSegments M)
    {K F : Set M} (hF : F.Nonempty) {R : ℝ} (hR : 0 < R)
    (hmax : ∀ y ∈ K, infDist y F ≤ R) :
    interior {y ∈ K | R ≤ infDist y F} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxS := interior_subset hx
  have hxdepth : infDist x F = R := le_antisymm (hmax x hxS.1) hxS.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let δ : ℝ := min ε R / 2
  have hδ : 0 < δ := half_pos (lt_min hε hR)
  have hδε : δ < ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left ε R)
  have hδR : δ < R := (half_lt_self (lt_min hε hR)).trans_le (min_le_right ε R)
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hF).mp
    (show infDist x F < R + δ / 2 by rw [hxdepth]; linarith)
  have hRxy : R ≤ dist x y := hxdepth ▸ infDist_le_dist_of_mem hy
  obtain ⟨σ, hσ0, hσy, hσ⟩ := hseg x y
  have h0 : (0 : ℝ) ∈ Icc 0 (dist x y) := ⟨le_rfl, dist_nonneg⟩
  have hδI : δ ∈ Icc 0 (dist x y) := ⟨hδ.le, hδR.le.trans hRxy⟩
  have hyI : dist x y ∈ Icc 0 (dist x y) := ⟨dist_nonneg, le_rfl⟩
  have hnear : dist (σ δ) x = δ := by
    simpa only [hσ0, sub_zero, abs_of_pos hδ] using hσ hδI h0
  have htail : dist (σ δ) y = dist x y - δ := by
    simpa only [hσy, abs_of_nonpos (sub_nonpos.mpr hδI.2), neg_sub] using hσ hδI hyI
  have hzS : σ δ ∈ {y ∈ K | R ≤ infDist y F} :=
    hball (mem_ball.mpr (by rw [hnear]; exact hδε))
  have hzF : infDist (σ δ) F ≤ dist x y - δ :=
    htail ▸ infDist_le_dist_of_mem hy
  linarith [hzS.2]

end Poincare.Riemannian.Soul
