import PoincareConjecture.Proofs.M08.ChartMinimizerRegularity
import PoincareConjecture.Proofs.M08.ChartCoverAt
import PoincareConjecture.Proofs.M08.LocalChartLimit
import PoincareConjecture.Proofs.M08.MinimizerPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [mTop : TopologicalSpace M]
  [mChart : ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [mSmooth : IsManifold (𝓡 n) ∞ M] [mConnected : ConnectedSpace M] [mT3 : T3Space M]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem minimizing_uniform_limit_contMDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax) (p₁ p₂ : M)
    (p : ℕ → BackwardTimePath F T τ₁ τ₂)
    (hanti : Antitone (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve))
    (hmin : Tendsto (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve)
      atTop (𝓝 (sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂))))
    (γ : ℝ → M) (hγ : Continuous γ)
    (hγa : γ (Real.sqrt τ₁) = p₁) (hγb : γ (Real.sqrt τ₂) = p₂)
    (hlim : letI : MetricSpace M := referenceMetricSpace (F.metric T)
      TendstoUniformlyOn (fun k ↦ squareReparameterizedCurve (p k).curve) γ atTop
        (Icc (Real.sqrt τ₁) (Real.sqrt τ₂))) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  intro s hs
  obtain ⟨m, t, x, K, j, ht, hta, htb, hK, haj, hjs, hsj, hjb⟩ :=
    exists_compact_partition_at
      (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
      (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source)
      (fun y ↦ ⟨y, mem_chart_source _ y⟩) hs γ hγ
  obtain ⟨w, hw, hsum⟩ := @finite_chart_limit_le_inf n M mTop mChart mSmooth
    mConnected mT3 J F T τmax τ₁ τ₂ hM04 hwindow hcurvature hτ₁ hordered hτ₂
    p₁ p₂ p hanti hmin γ hγ hlim m t ht hta htb x K hK
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source :=
    fun r hr ↦ (hK i).2.2 (interior_subset ((hK i).2.1 (mem_image_of_mem γ hr)))
  have hsum' : (∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      sInf (backwardActionValues F T τ₁ τ₂ (γ (t 0)) (γ (t (Fin.last m)))) := by
    simpa only [chartH1Action, hta, htb, hγa, hγb] using hsum
  have hlocal : IsChartH1Minimizer F T (x j) (t j.castSucc) (t j.succ) γ (w j) := by
    intro ξ hξ hξa hξb hξsrc v hv
    exact chart_piece_minimal hM04 hT hwindow hcurvature hτ₁ hordered hτ₂
      t ht hta htb γ hγ.continuousOn x hsrc w hw hsum' j ξ hξ hξa hξb hξsrc v hv
  have htime (r : ℝ) (hr : r ∈ Icc (t j.castSucc) (t j.succ)) :
      T - r ^ 2 ∈ interior J :=
    backwardSquareTime_mem_interior hwindow hτ₁ hordered hτ₂
      ⟨haj.trans_le hr.1, hr.2.trans_lt hjb⟩
  have hreg := chart_minimum_contDiffOn F hM04 T (hjs.trans hsj) (x j) γ hγ.continuousOn
    (hsrc j) htime (w j) (hw j) hlocal
  exact (chart_contMDiffAt_of_contDiffOn ⟨hjs, hsj⟩ (x j) γ (hsrc j) hreg).contMDiffWithinAt

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_minimizing_backward_path {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax) (p₁ p₂ : M) :
    ∃ p : BackwardTimePath F T τ₁ τ₂,
      p.curve τ₁ = p₁ ∧ p.curve τ₂ = p₂ ∧ IsMinimizingBackwardLPath F T τ₁ τ₂ p := by
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  obtain ⟨p, γ, _, hanti, hmin, hγ, hγa, hγb, hlim⟩ :=
    @exists_backward_minimizing_uniform_limit n M mTop mChart mSmooth mConnected mT3
      J F T τmax τ₁ τ₂ hM04 hT hwindow hcurvature hτ₁ hordered hτ₂ p₁ p₂
  have hreg := @minimizing_uniform_limit_contMDiffOn n M mTop mChart mSmooth
    mConnected mT3 J F T τmax τ₁ τ₂ hM04 hT hwindow hcurvature hτ₁ hordered hτ₂
    p₁ p₂ p hanti hmin γ hγ hγa hγb hlim
  obtain ⟨m, t, x, K, _, ht, hta, htb, hK, _⟩ :=
    exists_compact_partition_of_uniform_limit
      (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
      (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source)
      (fun y ↦ ⟨y, mem_chart_source _ y⟩) (Real.sqrt_lt_sqrt hτ₁ hordered).le γ hγ
      (fun k ↦ squareReparameterizedCurve (p k).curve) hlim
  obtain ⟨w, hw, hsum⟩ := @finite_chart_limit_le_inf n M mTop mChart mSmooth
    mConnected mT3 J F T τmax τ₁ τ₂ hM04 hwindow hcurvature hτ₁ hordered hτ₂
    p₁ p₂ p hanti hmin γ hγ hlim m t ht hta htb x K hK
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source :=
    fun r hr ↦ (hK i).2.2 (interior_subset ((hK i).2.1 (mem_image_of_mem γ hr)))
  have hreg' : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (t 0) (t (Fin.last m))) := by
    simpa only [hta, htb] using hreg
  obtain ⟨q, hqa, hqb, hqmin, _, _⟩ := exists_minimizing_backward_path_of_chart_limit
    hM04 hT hwindow hcurvature hτ₁ hordered hτ₂ t ht hta htb γ hγ.continuousOn hreg'
    p₁ p₂ hγa hγb x hsrc w hw hsum
  exact ⟨q, hqa, hqb, hqmin⟩

end PoincareConjecture.M08
