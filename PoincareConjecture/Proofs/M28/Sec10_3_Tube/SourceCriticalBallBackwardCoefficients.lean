import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardJets
import PoincareConjecture.Proofs.M28.Mathlib.WithinSmoothCompactness
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetsOfAmbient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}
  (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)

def limitDomain : Set (EuclideanSpace ℝ (Fin 3)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact ball (extChartAt (𝓡 3) q q) D.radius

theorem limitDomain_open : IsOpen D.limitDomain := isOpen_ball

theorem limitDomain_convex : Convex ℝ D.limitDomain := convex_ball _ _

instance limitDomain_nonempty : Nonempty D.limitDomain := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact ⟨⟨extChartAt (𝓡 3) q q, mem_ball_self D.radius_pos⟩⟩

theorem limitDomain_subset_testSet : D.limitDomain ⊆ D.testSet := ball_subset_closedBall

theorem limitDomain_subset_domain : D.limitDomain ⊆ D.domain :=
  D.limitDomain_subset_testSet.trans D.testSet_subset_domain

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2000000 in

theorem exists_backward_coefficient_limit {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k t, t ∈ Icc (-(a / 8)) 0 → ∀ x : strongNeckOpen (D.neck k),
      ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K)
    (hderiv : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ k t, t ∈ Icc (-(a / 8)) 0 →
      ∀ x ∈ D.domain, ((D.sourceFlow k).connection t).curvatureDerivativeNorm m
        (D.parametrization k x) ≤ B) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∃ eta : ℕ → ℕ, StrictMono eta ∧
      ∃ B : ℝ × EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ,
        ContDiffOn ℝ ∞ B (Icc (-(a / 8)) 0 ×ˢ D.limitDomain) ∧
        (∀ m L, IsCompact L → L ⊆ Icc (-(a / 8)) 0 ×ˢ D.limitDomain →
          TendstoUniformlyOn
            (fun k => iteratedFDerivWithin ℝ m
              (fun z => ((D.sourceFlow (eta k)).metric z.1).pullbackCoefficients
                (D.parametrization (eta k)) z.2) (Icc (-(a / 8)) 0 ×ˢ D.limitDomain))
            (iteratedFDerivWithin ℝ m B (Icc (-(a / 8)) 0 ×ˢ D.limitDomain)) atTop L) ∧
        ∀ x ∈ D.limitDomain, B (0, x) =
          G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) q).symm x := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let J := Icc (-(a / 8)) 0
  let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
    ((D.sourceFlow k).metric z.1).pullbackCoefficients (D.parametrization k) z.2
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by linarith [D.scale_pos])
  let : LocallyCompactSpace J := isClosed_Icc.locallyCompactSpace
  let : LocallyCompactSpace D.limitDomain := D.limitDomain_open.locallyCompactSpace
  let : ∀ _ : ℕ, LocallyCompactSpace (J ×ˢ D.limitDomain) := fun _ =>
    (Homeomorph.Set.prod J D.limitDomain).isOpenEmbedding.locallyCompactSpace
  have hsmooth (k : ℕ) : ContDiffOn ℝ ∞ (f k) (J ×ˢ D.limitDomain) :=
    (D.sourceFlow k).smooth.contDiffOn_spacetime_pullbackCoefficients_within
      D.limitDomain_open ((D.parametrization_smooth k).mono D.limitDomain_subset_domain)
  have hbound : ∀ (_ : ℕ) (L : Set (ℝ × EuclideanSpace ℝ (Fin 3))),
      IsCompact L → L ⊆ J ×ˢ D.limitDomain → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ z ∈ L,
        ‖iteratedFDerivWithin ℝ m (f k) (J ×ˢ D.limitDomain) z‖ ≤ B := by
    intro _ L _ hL m
    obtain ⟨B, _, hB⟩ := D.mixed_jet_bounds hK hcurv hderiv m
    refine ⟨B, hB.mono (fun k hk z hz => ?_)⟩
    rw [iteratedFDerivWithin_prod_eq_of_isOpen (f k) m D.limitDomain_open D.domain_open
      (hL hz).2 (D.limitDomain_subset_domain (hL hz).2)]
    exact hk z ⟨(hL hz).1, D.limitDomain_subset_testSet (hL hz).2⟩
  obtain ⟨eta, heta, B, hB, hjets⟩ :=
    exists_common_contDiffOn_subsequence_of_withinJet_bounds
      (fun _ : ℕ => J ×ˢ D.limitDomain)
      (fun _ => (convex_Icc (-(a / 8)) 0).prod D.limitDomain_convex)
      (fun _ => hJ.prod D.limitDomain_open.uniqueDiffOn)
      (fun _ : ℕ => f) (fun _ => hsmooth) hbound
  refine ⟨eta, heta, B 0, hB 0, hjets 0, ?_⟩
  intro x hx
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith [D.scale_pos], le_rfl⟩
  have hpoint : ({(0, x)} : Set (ℝ × EuclideanSpace ℝ (Fin 3))) ⊆
      J ×ˢ D.limitDomain := singleton_subset_iff.mpr ⟨hzero, hx⟩
  have hcoeff := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn
      (hjets 0 0 {(0, x)} isCompact_singleton hpoint)
  have htime : Tendsto (fun k => f (eta k) (0, x)) atTop (𝓝 (B 0 (0, x))) := by
    simpa only [Function.comp_apply, iteratedFDerivWithin_zero_apply] using
      hcoeff.tendsto_at (mem_singleton (0, x))
  have htarget : ({x} : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (extChartAt (𝓡 3) q).target :=
    singleton_subset_iff.mpr (D.target (ball_subset_closedBall (D.limitDomain_subset_domain hx)))
  have hspatial := (G.tendstoUniformlyOn_chart_coefficients q {x}
    isCompact_singleton htarget).tendsto_at (mem_singleton x)
  have hspatial' : Tendsto (fun k => f (eta k) (0, x)) atTop
      (𝓝 (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) q).symm x)) := by
    apply (hspatial.comp ((tendsto_add_atTop_nat D.offset).comp heta.tendsto_atTop)).congr'
    exact Eventually.of_forall (fun k =>
      (D.terminal_coefficients (eta k) (D.limitDomain_subset_domain hx)).symm)
  exact tendsto_nhds_unique htime hspatial'

end PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
