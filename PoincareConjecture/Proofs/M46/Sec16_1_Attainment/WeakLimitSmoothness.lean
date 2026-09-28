import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.AnchoredWeakMinimum
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePrimitiveRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}




theorem weak_limit_contMDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (p : ℕ → M14BackwardPath G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn (fun k r => (p k).curve (r ^ 2)) gamma atTop (Icc 0 (Real.sqrt tau)))
    {D : ℝ} (henergy : ∀ k,
      IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ r in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) r) ≤ D)
    (haction : Tendsto (fun k => M14BackwardLAction G (p k)) atTop
      (𝓝 (M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau))))) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ gamma (Icc 0 (Real.sqrt tau)) := by
  have hS : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hmiddle : Real.sqrt tau / 2 ∈ Ioo 0 (Real.sqrt tau) :=
    ⟨half_pos hS, half_lt_self hS⟩
  obtain ⟨R, hR, _⟩ := exists_anchored_weak_minimum hM12 hmiddle p gamma hgamma hlim henergy haction
  have hRspan : R.node 0 < R.node (Fin.last R.count) := by rw [R.first, R.last]; exact hS
  have hpiece (j : Fin R.count) (hj : R.node j.castSucc < R.node j.succ) :=
    gauge_primitive_piece_contMDiffOn hM12 htau gamma hgamma hclock R hfinite hR j hj
  intro s hs
  by_cases hzero : s = 0
  · subst s
    obtain ⟨j, hj, hz⟩ := positive_partition_covers R.node R.monotone hRspan
      (by simpa only [R.first, R.last] using hs)
    have hleft : R.node j.castSucc = 0 := le_antisymm hz.1
      (by simpa only [R.first] using R.monotone (Fin.zero_le j.castSucc))
    have hnear : Icc (R.node j.castSucc) (R.node j.succ) ∈ 𝓝[Icc 0 (Real.sqrt tau)] 0 := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨Iio (R.node j.succ), Iio_mem_nhds (by simpa only [hleft] using hj), ?_⟩
      intro z hz
      exact ⟨by simpa only [hleft] using hz.2.1, hz.1.le⟩
    exact (hpiece j hj 0 hz).mono_of_mem_nhdsWithin hnear
  · by_cases hlast : s = Real.sqrt tau
    · subst s
      obtain ⟨j, hj, hz⟩ := positive_partition_covers R.node R.monotone hRspan
        (by simpa only [R.first, R.last] using hs)
      have hright : R.node j.succ = Real.sqrt tau := le_antisymm
        (by simpa only [R.last] using R.monotone (Fin.le_last j.succ)) hz.2
      have hnear : Icc (R.node j.castSucc) (R.node j.succ) ∈
          𝓝[Icc 0 (Real.sqrt tau)] (Real.sqrt tau) := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        refine ⟨Ioi (R.node j.castSucc), Ioi_mem_nhds (by simpa only [hright] using hj), ?_⟩
        intro z hz
        exact ⟨hz.1.le, by simpa only [hright] using hz.2.2⟩
      exact (hpiece j hj _ hz).mono_of_mem_nhdsWithin hnear
    · have hsint : s ∈ Ioo 0 (Real.sqrt tau) :=
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hzero), lt_of_le_of_ne hs.2 hlast⟩
      obtain ⟨Q, hQ, j, hjs, hsj⟩ := exists_anchored_weak_minimum hM12 hsint p gamma
        hgamma hlim henergy haction
      have hq := gauge_primitive_piece_contMDiffOn hM12 htau gamma hgamma hclock Q
        hfinite hQ j (hjs.trans hsj)
      exact ((hq s ⟨hjs.le, hsj.le⟩).contMDiffAt (Icc_mem_nhds hjs hsj)).contMDiffWithinAt

end PoincareConjecture.Proofs.M46
