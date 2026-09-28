import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RescaledSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RoundFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Classification








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

private theorem round_of_pullbackDiffeomorph
    {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (F : RicciFlow n N J) (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ)
    (hround : ConstantPositiveSectionalCurvature
      ((F.pullbackDiffeomorph e).metric t) ((F.pullbackDiffeomorph e).connection t)) :
    ConstantPositiveSectionalCurvature (F.metric t) (F.connection t) := by
  obtain ⟨k, hk, hr⟩ := hround
  refine ⟨k, hk, fun x u v hu hv huv => ?_⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  let T := e.mfderivToContinuousLinearEquiv (by simp) y
  have hT (a : TangentSpace (𝓡 n) (e y)) :
      mfderiv (𝓡 n) (𝓡 n) e y (T.symm a) = a := T.apply_symm_apply a
  have hnorm (a b : TangentSpace (𝓡 n) (e y)) :
      ((F.pullbackDiffeomorph e).metric t).inner y (T.symm a) (T.symm b) =
        (F.metric t).inner (e y) a b := by
    rw [F.pullbackDiffeomorph_inner, hT, hT]
  have hcurv := ((F.pullbackDiffeomorph e).connection t).curvatureTensor_eq_of_local_isometry
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun z _ a b => F.pullbackDiffeomorph_inner e t z a b) (mem_univ y)
    (T.symm u) (T.symm v) (T.symm u) (T.symm v)
  simp only [hT] at hcurv
  have hr' := hr y (T.symm u) (T.symm v)
    ((hnorm u u).trans hu) ((hnorm v v).trans hv) ((hnorm u v).trans huv)
  change (F.connection t).sectionalCurvature (e y) u v = k
  simpa only [LeviCivitaData.sectionalCurvature, hnorm, hcurv] using hr'

namespace AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  uliftSecondCountable uliftConnected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem constantPositiveSectionalCurvature_of_compact
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    [CompactSpace L.convergence.limit.carrier.carrier] (t : ℝ) (ht : t < 0) :
    ConstantPositiveSectionalCurvature (L.convergence.limit.flow.metric t)
      (L.convergence.limit.flow.connection t) := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let : CompactSpace (ULift.{u} L.convergence.limit.carrier.carrier) :=
    Homeomorph.ulift.symm.compactSpace
  let F := L.convergence.limit.flow
  let H : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  let A := L.normalizedShrinkingSolitonData hC t ht
    (L.convergence.limit.bounded_curvature_of_compact hC t ht)
  have hround := A.constantPositiveSectionalCurvature_of_compact hC
  let E : HomotheticMetricSlice A.metric (H.metric t) |t| :=
    { map := Diffeomorph.refl (𝓡 3) _ ∞
      inner_eq := by
        intro x a b
        simp only [Diffeomorph.coe_refl, mfderiv_id]
        change (H.metric t).inner x a b =
          |t| * (rescaledMetric (H.metric t) |t|⁻¹ (inv_pos.mpr (abs_pos.mpr ht.ne))).inner x a b
        rw [rescaledMetric_inner, ← mul_assoc, mul_inv_cancel₀ (abs_pos.mpr ht.ne).ne', one_mul] }
  have hH := E.constantPositiveSectionalCurvature_three (abs_pos.mpr ht.ne)
    A.connection (H.connection t) hround
  exact round_of_pullbackDiffeomorph F
    (Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier) t hH


theorem classificationCertificate_of_compact
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    [CompactSpace L.convergence.limit.carrier.carrier] :
    ThreeDimensionalAsymptoticClassificationCertificate S L :=
  L.classificationCertificate_of_compact_round hC
    (L.constantPositiveSectionalCurvature_of_compact hC)

end AncientAsymptoticSolitonLimitData

end PoincareConjecture
