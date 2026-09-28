import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedCurvatureBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedMixedBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedExtension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.secondCountable

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_finite_terminal_extension_of_big_window_bounds
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    {T Tbig tau B : ℝ} (htau : 0 < tau) (htauT : tau < T)
    (hT1 : T ≤ 1) (hTT : T < Tbig)
    {S : PointedFlowSequence 3 (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (Fbig : ∀ k, RicciFlow 3 (S.carrier k).carrier (Icc (-Tbig) 0))
    (hmetric : ∀ k t, (Fbig k).metric t =
      (S.flow k).flow.metric (t + T / 2))
    (hcurv : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-Tbig) 0,
      ∀ x : (S.carrier k).carrier,
        ((Fbig k).connection t).curvatureTensorNorm x ≤ B)
    (hcompact : ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (((Fbig k).metric 0).ball (S.flow k).base R))) :
    let f := fun (q : G.limitCarrier.carrier) (k : ℕ)
        (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
      ((Fbig (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 3) q).symm) z.2
    ∃ F : RicciFlow 3 G.limitCarrier.carrier (Icc (-tau) 0),
      (∀ t ∈ Ico (-tau) 0,
        F.metric t = G.limitFlow.flow.metric (t + T / 2)) ∧
      ∀ (q : G.limitCarrier.carrier) (m : ℕ)
        (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))),
        IsCompact K → K ⊆ Icc (-tau) 0 ×ˢ (extChartAt (𝓡 3) q).target →
        TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m (f q k)
            (Icc (-tau) 0 ×ˢ (extChartAt (𝓡 3) q).target))
          (iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
              (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2)
            (Icc (-tau) 0 ×ˢ (extChartAt (𝓡 3) q).target)) atTop K := by
  intro f
  have hT : 0 < T := htau.trans htauT
  have hsmall : Icc (-T) (0 : ℝ) ⊆ Icc (-Tbig) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hne : (Icc (-T) (0 : ℝ)).Nontrivial :=
    ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  let Fsrc (k : ℕ) : RicciFlow 3 (S.carrier k).carrier (Icc (-T) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (Fbig k) hsmall ordConnected_Icc hne
  have hm : ∀ k t, (Fsrc k).metric t = (S.flow k).flow.metric (t + T / 2) := hmetric
  have href (k : ℕ) : (Fbig k).metric (-T / 2) = (S.flow k).metricAt 0 := by
    change (Fbig k).metric (-T / 2) = (S.flow k).flow.metric 0
    rw [hmetric]
    congr 1
    ring
  apply exists_finite_terminal_extension_on_retained_carrier hFlow htau htauT G Fsrc hm
  apply exists_retained_local_coefficient_bounds hMixed htau htauT hT1 G Fsrc hm
  intro q K hK hKc j
  have himage := hK.image_of_continuousOn
    ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc)
  obtain ⟨D, hD, hbound⟩ := exists_eventually_retained_curvature_derivative_bound
    hShi hT hTT G hcomplete Fbig href hcurv hcompact himage j
  refine ⟨D, hD.le, ?_⟩
  filter_upwards [hbound] with k hk t ht x hx
  exact hk t ht ((extChartAt (𝓡 3) q).symm x) (mem_image_of_mem _ hx)

end PoincareConjecture.M30
