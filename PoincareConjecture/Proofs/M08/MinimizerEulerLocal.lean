import PoincareConjecture.Proofs.M08.CompleteMinimizer
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [mTop : TopologicalSpace M]
  [mChart : ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [mSmooth : IsManifold (𝓡 n) ∞ M]

theorem backwardActionValues_isLeast_of_minimizing {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (hp : IsMinimizingBackwardLPath F T τ₁ τ₂ p) :
    IsLeast (backwardActionValues F T τ₁ τ₂ (p.curve τ₁) (p.curve τ₂))
      (backwardLLength F T τ₁ τ₂ p.curve) := by
  refine ⟨⟨p, rfl, rfl, rfl⟩, ?_⟩
  rintro L ⟨q, hqa, hqb, rfl⟩
  exact hp q hqa hqb

theorem exists_continuous_squarePath_extension {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) :
    ∃ γ : ℝ → M, Continuous γ ∧
      EqOn γ (squareReparameterizedCurve p.curve) (Icc (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
  let A := Real.sqrt τ₁
  let B := Real.sqrt τ₂
  have hAB : A ≤ B := Real.sqrt_le_sqrt p.ordered.le
  let f : Icc A B → M := fun s ↦ squareReparameterizedCurve p.curve s
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp (squarePath_continuousOn p)
  refine ⟨f ∘ projIcc A B hAB, hf.comp continuous_projIcc, ?_⟩
  intro s hs
  simp only [Function.comp_apply, projIcc_of_mem hAB hs, f]

section Metric

variable {X : Type u} [MetricSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]

theorem chartH1Action_congr {J : Set ℝ} {F : RicciFlow n X J}
    {T a b : ℝ} (hab : a ≤ b) (x : X) {α β : ℝ → X}
    (h : EqOn α β (Icc a b)) (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b) :
    chartH1Action F T x a b α w = chartH1Action F T x a b β w := by
  unfold chartH1Action
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro s hs <;>
    dsimp only <;>
    rw [h ((uIcc_of_le hab ▸ hs) : s ∈ Icc a b)]

theorem isChartH1Minimizer_congr {J : Set ℝ} {F : RicciFlow n X J}
    {T a b : ℝ} (hab : a ≤ b) (x : X) {α β : ℝ → X}
    (h : EqOn α β (Icc a b)) (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hmin : IsChartH1Minimizer F T x a b α w) :
    IsChartH1Minimizer F T x a b β w := by
  intro ξ hξ hξa hξb hξsrc v hv
  rw [← chartH1Action_congr hab x h w]
  exact hmin ξ hξ (hξa.trans (h ⟨le_rfl, hab⟩).symm)
    (hξb.trans (h ⟨hab, le_rfl⟩).symm) hξsrc v hv

end Metric

variable [mConnected : ConnectedSpace M] [mT3 : T3Space M]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem minimizing_squarePath_local_minimum {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ s : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsMinimizingBackwardLPath F T τ₁ τ₂ p)
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    letI : MetricSpace M := referenceMetricSpace (F.metric T)
    ∃ (a b : ℝ) (x : M) (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b),
      Real.sqrt τ₁ < a ∧ a < s ∧ s < b ∧ b < Real.sqrt τ₂ ∧
      MapsTo (squareReparameterizedCurve p.curve) (Icc a b)
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      (∀ r ∈ Icc a b, extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve r) =
        extChartAt (𝓡 n) x (squareReparameterizedCurve p.curve a) + ∫ q in a..r, w q) ∧
      IsChartH1Minimizer F T x a b (squareReparameterizedCurve p.curve) w := by
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  obtain ⟨γ, hγ, hγeq⟩ := exists_continuous_squarePath_extension p
  have hγa : γ (Real.sqrt τ₁) = p.curve τ₁ := by
    rw [hγeq ⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩]
    simp only [squareReparameterizedCurve, Real.sq_sqrt p.nonnegative]
  have hγb : γ (Real.sqrt τ₂) = p.curve τ₂ := by
    rw [hγeq ⟨Real.sqrt_le_sqrt p.ordered.le, le_rfl⟩]
    simp only [squareReparameterizedCurve, Real.sq_sqrt (p.nonnegative.trans p.ordered.le)]
  have hanti : Antitone (fun _ : ℕ ↦ backwardLLength F T τ₁ τ₂ p.curve) :=
    fun _ _ _ ↦ le_rfl
  have hmin : Tendsto (fun _ : ℕ ↦ backwardLLength F T τ₁ τ₂ p.curve)
      atTop (𝓝 (sInf (backwardActionValues F T τ₁ τ₂ (p.curve τ₁) (p.curve τ₂)))) := by
    rw [(backwardActionValues_isLeast_of_minimizing hp).csInf_eq]
    exact tendsto_const_nhds
  have hlim : TendstoUniformlyOn (fun _ : ℕ ↦ squareReparameterizedCurve p.curve) γ atTop
      (Icc (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ r hr ↦ by simpa only [hγeq hr, dist_self] using hε)
  obtain ⟨m, t, x, K, j, ht, hta, htb, hK, haj, hjs, hsj, hjb⟩ :=
    exists_compact_partition_at
      (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
      (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source)
      (fun y ↦ ⟨y, mem_chart_source _ y⟩) hs γ hγ
  obtain ⟨w, hw, hsum⟩ := @finite_chart_limit_le_inf n M mTop mChart mSmooth
    mConnected mT3 J F T τmax τ₁ τ₂ hM04 hwindow hcurvature p.nonnegative p.ordered hτ₂
    (p.curve τ₁) (p.curve τ₂) (fun _ ↦ p) hanti hmin γ hγ hlim m t ht hta htb x K hK
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source :=
    fun r hr ↦ (hK i).2.2 (interior_subset ((hK i).2.1 (mem_image_of_mem γ hr)))
  have hsum' : (∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      sInf (backwardActionValues F T τ₁ τ₂ (γ (t 0)) (γ (t (Fin.last m)))) := by
    simpa only [chartH1Action, hta, htb, hγa, hγb] using hsum
  have hlocal : IsChartH1Minimizer F T (x j) (t j.castSucc) (t j.succ) γ (w j) := by
    intro ξ hξ hξa hξb hξsrc v hv
    exact chart_piece_minimal hM04 p.terminal_mem hwindow hcurvature p.nonnegative p.ordered hτ₂
      t ht hta htb γ hγ.continuousOn x hsrc w hw hsum' j ξ hξ hξa hξb hξsrc v hv
  have heq : EqOn γ (squareReparameterizedCurve p.curve) (Icc (t j.castSucc) (t j.succ)) :=
    hγeq.mono (Icc_subset_Icc haj.le hjb.le)
  have hab : t j.castSucc ≤ t j.succ := (hjs.trans hsj).le
  refine ⟨t j.castSucc, t j.succ, x j, w j, haj, hjs, hsj, hjb, ?_, ?_, ?_⟩
  · intro r hr
    rw [← heq hr]
    exact hsrc j hr
  · intro r hr
    rw [← heq hr, ← heq ⟨le_rfl, hab⟩]
    exact hw j r hr
  · exact isChartH1Minimizer_congr hab (x j) heq (w j) hlocal

end PoincareConjecture.M08
