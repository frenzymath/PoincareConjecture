import PoincareConjecture.Proofs.M08.JacobiLocalExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance jacobiUniqueDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiUniqueDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiUniqueBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiUniqueBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def chartPairCoordinates (x : M) (α : ℝ → M)
    (z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  ((e (Bundle.TotalSpace.mk' (E := TangentSpace (𝓡 n))
    (EuclideanSpace ℝ (Fin n)) (α s) (z s).1)).2,
    (e (Bundle.TotalSpace.mk' (E := TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n)) (α s) (z s).2)).2)

theorem chartFrame_coordinates_at {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v : TangentSpace (𝓡 n) y) :
    chartFrame x
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
        (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y v)).2) y = v := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  change e.symmL ℝ y ((e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y v)).2) = v
  rw [e.symmL_apply (R := ℝ) hy]
  exact e.symm_apply_apply_mk hy v

theorem chartFrame_injective_of_mem {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    Function.Injective (fun v : EuclideanSpace ℝ (Fin n) ↦ chartFrame x v y) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  intro v w hvw
  have h := congrArg (e.continuousLinearMapAt ℝ y) hvw
  change e.continuousLinearMapAt ℝ y (e.symmL ℝ y v) =
    e.continuousLinearMapAt ℝ y (e.symmL ℝ y w) at h
  simpa only [e.continuousLinearMapAt_symmL hy] using h

theorem IsJacobiPairOn.chart_coordinates_smooth {J S : Set ℝ} {F : RicciFlow n M J}
    {T a b : ℝ} {α : ℝ → M}
    {z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (h : IsJacobiPairOn F T α S a b z) (x : M)
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContDiffOn ℝ ∞ (chartPairCoordinates x α z) (Icc a b) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hfirst := e.contMDiffOn.comp h.first_smooth (fun s hs ↦ e.mem_source.mpr (hsrc hs))
  have hsecond := e.contMDiffOn.comp h.second_smooth (fun s hs ↦ e.mem_source.mpr (hsrc hs))
  exact (ContMDiffOn.contDiffOn (fun s hs ↦ (hfirst s hs).snd)).prodMk
    (ContMDiffOn.contDiffOn (fun s hs ↦ (hsecond s hs).snd))

set_option maxHeartbeats 2500000 in
theorem IsJacobiPairOn.chart_phase {J U : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T A B a b : ℝ} {α : ℝ → M}
    {z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (h : IsJacobiPairOn F T α (Icc A B) a b z) (hAB : A < B)
    (htime : ∀ s ∈ Icc A B, T - s ^ 2 ∈ J)
    (x : M) (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ∀ s ∈ Icc a b, HasDerivWithinAt (chartPairCoordinates x α z)
      (jacobiAlongPhase F T x (Icc A B) α s (chartPairCoordinates x α z s)) (Icc a b) s := by
  let v := chartPairCoordinates x α z
  have hv : ContDiffOn ℝ ∞ v (Icc a b) := h.chart_coordinates_smooth x hsrc
  have hframe₁ : ∀ s ∈ Icc a b, chartFrame x (v s).1 (α s) = (z s).1 :=
    fun s hs ↦ chartFrame_coordinates_at (hsrc hs) (z s).1
  have hframe₂ : ∀ s ∈ Icc a b, chartFrame x (v s).2 (α s) = (z s).2 :=
    fun s hs ↦ chartFrame_coordinates_at (hsrc hs) (z s).2
  obtain ⟨EY, EP, hY, hP⟩ := h.equations
  intro s hs
  have hαs := ((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).mdifferentiableAt (by simp)
  let dy := derivWithin (fun r ↦ (v r).1) (Icc a b) s
  let dp := derivWithin (fun r ↦ (v r).2) (Icc a b) s
  have hdy : HasDerivWithinAt (fun r ↦ (v r).1) dy (Icc a b) s :=
    ((hv.fst.differentiableOn (by simp)) s hs).hasDerivWithinAt
  have hdp : HasDerivWithinAt (fun r ↦ (v r).2) dp (Icc a b) s :=
    ((hv.snd.differentiableOn (by simp)) s hs).hasDerivWithinAt
  have hDY := pullbackCovariantDerivative_closedChart_formula F T h.ordered h.interval_subset
    htime x α (fun r ↦ (v r).1) hv.fst hsrc (fun r ↦ (z r).1) hframe₁ EY hs dy hdy hαs
  have hDP := pullbackCovariantDerivative_closedChart_formula F T h.ordered h.interval_subset
    htime x α (fun r ↦ (v r).2) hv.snd hsrc (fun r ↦ (z r).2) hframe₂ EP hs dp hdp hαs
  have hq : extChartAt (𝓡 n) x (α s) ∈ (extChartAt (𝓡 n) x).target :=
    (extChartAt (𝓡 n) x).map_source (by simpa only [extChartAt_source] using hsrc hs)
  have hfirst : dy = (v s).2 - jacobiAlongConnection F T x (Icc A B) α s (v s).1 := by
    apply eq_sub_iff_add_eq.mpr
    apply chartFrame_injective_of_mem (hsrc hs)
    exact hDY.symm.trans ((hY s hs).trans (hframe₂ s hs).symm)
  have hsecond (w : EuclideanSpace ℝ (Fin n)) :
      chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s))
          (dp + jacobiAlongConnection F T x (Icc A B) α s (v s).2) w =
        jacobiAlongPotential F T x (Icc A B) α s (v s).1 w -
          jacobiAlongMetricTime F T x (Icc A B) α s (v s).2 w := by
    have hr := hP s hs (chartFrame x w (α s))
    rw [hDP, ← hframe₁ s hs, ← hframe₂ s hs] at hr
    rw [jacobiPairResidual_chart F hM04 T hAB htime x α (h.interval_subset hs)
      (hsrc hs) hαs] at hr
    change chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s))
        (dp + jacobiAlongConnection F T x (Icc A B) α s (v s).2) w -
      jacobiAlongPotential F T x (Icc A B) α s (v s).1 w +
        jacobiAlongMetricTime F T x (Icc A B) α s (v s).2 w = 0 at hr
    linarith
  have heq := covariantLinearPhaseOperator_eq_of_pair (jacobiAlongSharp F T x α s)
    (chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s)))
    (chartMetricDualInverse_left F T x hq)
    (jacobiAlongConnection F T x (Icc A B) α s)
    (jacobiAlongPotential F T x (Icc A B) α s)
    (jacobiAlongMetricTime F T x (Icc A B) α s)
    (v s).1 (v s).2 dy dp hfirst hsecond
  change HasDerivWithinAt v (covariantLinearPhaseOperator (jacobiAlongSharp F T x α s)
    (jacobiAlongConnection F T x (Icc A B) α s)
    (jacobiAlongPotential F T x (Icc A B) α s)
    (jacobiAlongMetricTime F T x (Icc A B) α s) ((v s).1, (v s).2)) (Icc a b) s
  rw [← heq]
  simpa only [Prod.eta] using hdy.prodMk hdp

theorem chartJacobiPairOn_unique {J U : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T A B a b t₀ : ℝ} {α : ℝ → M}
    {f g : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hf : IsJacobiPairOn F T α (Icc A B) a b f)
    (hg : IsJacobiPairOn F T α (Icc A B) a b g) (hAB : A < B)
    (htime : ∀ s ∈ Icc A B, T - s ^ 2 ∈ J)
    (x : M) (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht₀ : t₀ ∈ Icc a b) (hinit : f t₀ = g t₀) : EqOn f g (Icc a b) := by
  obtain ⟨hB, hC, hV, hH⟩ := jacobiAlongCoefficients_contDiffOn F hM04 T x α
    (uniqueDiffOn_Icc hAB) htime hf.interval_subset hU hCU hα hsrc
  have hcoordinit : chartPairCoordinates x α f t₀ = chartPairCoordinates x α g t₀ := by
    unfold chartPairCoordinates
    rw [hinit]
  have heq := covariant_linear_phase_unique (jacobiAlongSharp F T x α)
    (jacobiAlongConnection F T x (Icc A B) α) (jacobiAlongPotential F T x (Icc A B) α)
    (jacobiAlongMetricTime F T x (Icc A B) α) hB hC hV hH ht₀
    (hf.chart_phase hM04 hAB htime x hU hCU hα hsrc)
    (hg.chart_phase hM04 hAB htime x hU hCU hα hsrc) hcoordinit
  intro s hs
  apply Prod.ext
  · have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        chartFrame x v.1 (α s)) (heq hs)
    exact (chartFrame_coordinates_at (hsrc hs) (f s).1).symm.trans
      (h₁.trans (chartFrame_coordinates_at (hsrc hs) (g s).1))
  · have h₂ := congrArg (fun v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        chartFrame x v.2 (α s)) (heq hs)
    exact (chartFrame_coordinates_at (hsrc hs) (f s).2).symm.trans
      (h₂.trans (chartFrame_coordinates_at (hsrc hs) (g s).2))

end PoincareConjecture.M08
