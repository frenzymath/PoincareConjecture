import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Ancient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartCoverAt
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.PartitionLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.LocalMinimality









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

set_option maxHeartbeats 800000 in


theorem minimizing_uniform_limit_contMDiffOn (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (paths : ℕ → BackwardTimePath K.flow 0 0 τ)
    (hanti : Antitone (fun k => backwardLLength K.flow 0 0 τ (paths k).curve))
    (hmin : Tendsto (fun k => backwardLLength K.flow 0 0 τ (paths k).curve)
      atTop (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)))
    (γ : ℝ → M) (hγ : Continuous γ) (hγ0 : γ 0 = p)
    (hlim : TendstoUniformlyOn (fun k s => (paths k).curve (s ^ 2)) γ atTop
      (Icc 0 (Real.sqrt τ))) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ γ (Ioo 0 (Real.sqrt τ)) := by
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 2)
  intro s hs
  obtain ⟨m, t, x, Q, j, ht, hta, htb, hQ, _, hjs, hsj, _⟩ :=
    exists_compact_partition_at
      (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
      (fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source)
      (fun y => ⟨y, mem_chart_source _ y⟩) hs γ hγ
  obtain ⟨w, hw, hsum⟩ := K.finite_chart_limit_le_spatialInfimum p hτ paths
    hanti hmin γ hγ hlim t ht hta htb x Q hQ
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    fun r hr => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hr)))
  have hsum' : (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ := by
    simpa only [chartH1Action, hγ0] using hsum
  have hlocal : IsChartH1Minimizer K.flow 0 (x j) (t j.castSucc) (t j.succ) γ (w j) := by
    intro ξ hξ hξa hξb hξsrc v hv
    exact K.chart_piece_minimal hτ t ht hta htb γ hγ.continuousOn x hsrc w hw hsum'
      j ξ hξ hξa hξb hξsrc v hv
  have hreg := K.chart_minimum_contMDiffOn (hjs.trans hsj) (x j) γ hγ.continuousOn
    (hsrc j) (w j) (hw j) hlocal
  exact ((hreg s ⟨hjs.le, hsj.le⟩).contMDiffAt
    (Icc_mem_nhds hjs hsj)).contMDiffWithinAt

set_option maxHeartbeats 800000 in


theorem minimizing_uniform_limit_contMDiffOn_Icc (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (paths : ℕ → BackwardTimePath K.flow 0 0 τ)
    (hanti : Antitone (fun k => backwardLLength K.flow 0 0 τ (paths k).curve))
    (hmin : Tendsto (fun k => backwardLLength K.flow 0 0 τ (paths k).curve)
      atTop (𝓝 (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ)))
    (γ : ℝ → M) (hγ : Continuous γ) (hγ0 : γ 0 = p)
    (hlim : TendstoUniformlyOn (fun k s => (paths k).curve (s ^ 2)) γ atTop
      (Icc 0 (Real.sqrt τ))) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ γ (Icc 0 (Real.sqrt τ)) := by
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 2)
  obtain ⟨m, t, x, Q, _, ht, hta, htb, hQ, _⟩ :=
    exists_compact_partition_of_uniform_limit
      (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
      (fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source)
      (fun y => ⟨y, mem_chart_source _ y⟩) (Real.sqrt_nonneg τ) γ hγ
      (fun k s => (paths k).curve (s ^ 2)) hlim
  obtain ⟨w, hw, hsum⟩ := K.finite_chart_limit_le_spatialInfimum p hτ paths
    hanti hmin γ hγ hlim t ht hta htb x Q hQ
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    fun r hr => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hr)))
  have hsum' : (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ := by
    simpa only [chartH1Action, hγ0] using hsum
  have hlocal (j : Fin m) (hj : t j.castSucc < t j.succ) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ γ (Icc (t j.castSucc) (t j.succ)) := by
    apply K.chart_minimum_contMDiffOn hj (x j) γ hγ.continuousOn (hsrc j) (w j) (hw j)
    intro ξ hξ hξa hξb hξsrc v hv
    exact K.chart_piece_minimal hτ t ht hta htb γ hγ.continuousOn x hsrc w hw hsum'
      j ξ hξ hξa hξb hξsrc v hv
  have htpos : t 0 < t (Fin.last m) := by rw [hta, htb]; positivity
  have hleft : ContMDiffWithinAt (𝓘(ℝ, ℝ)) (𝓡 2) ∞ γ (Icc 0 (Real.sqrt τ)) 0 := by
    obtain ⟨j, hja, hjb⟩ := exists_first_strict_segment t ht htpos
    rw [hta] at hja hjb
    have hj : t j.castSucc < t j.succ := by simpa only [hja] using hjb
    have hreg := hlocal j hj
    rw [hja] at hreg
    apply (hreg 0 ⟨le_rfl, hjb.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hjb)] with r hr hrd
    exact ⟨hr.1, hrd.le⟩
  have hright : ContMDiffWithinAt (𝓘(ℝ, ℝ)) (𝓡 2) ∞ γ
      (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) := by
    obtain ⟨j, hjb, hja⟩ := exists_last_strict_segment t ht htpos
    rw [htb] at hjb hja
    have hj : t j.castSucc < t j.succ := by simpa only [hjb] using hja
    have hreg := hlocal j hj
    rw [hjb] at hreg
    apply (hreg (Real.sqrt τ) ⟨hja.le, le_rfl⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hja)] with r hr har
    exact ⟨har.le, hr.2⟩
  have hinterior := K.minimizing_uniform_limit_contMDiffOn p hτ paths hanti hmin γ hγ hγ0 hlim
  intro s hs
  rcases hs.1.eq_or_lt with h | h
  · simpa only [← h] using hleft
  rcases hs.2.eq_or_lt with heq | hlt
  · simpa only [heq] using hright
  exact ((hinterior s ⟨h, hlt⟩).contMDiffAt
    (isOpen_Ioo.mem_nhds ⟨h, hlt⟩)).contMDiffWithinAt

end PoincareConjecture.AncientKappaSolution
