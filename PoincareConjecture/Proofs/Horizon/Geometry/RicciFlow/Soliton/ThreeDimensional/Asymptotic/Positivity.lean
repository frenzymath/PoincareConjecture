import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Rank
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem scalarCurvature_pos_of_nonflat_ancient_slice
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iio 0))
    (hoperator : ∀ t < 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {t : ℝ} (ht : t < 0)
    (hnonflat : ∃ p, (F.connection t).curvatureTensorNorm p ≠ 0) (x : M) :
    0 < (F.connection t).scalarCurvature x := by
  obtain ⟨p, hp⟩ := hnonflat
  have hD := hC.tensor_calculus 3 M (F.metric t) (F.connection t)
  have hupper := (F.connection t).ricciNullity_le_one_of_nonflat hD p (hoperator t ht p) hp
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (t - 1) t ⊆ Iio 0 from fun _ hs => lt_of_le_of_lt hs.2 ht)
    ordConnected_Icc ⟨t - 1, by simp, t, by simp, by linarith⟩
  have hsec : ∀ s ∈ Icc (t - 1) t, (G.connection s).NonnegativeSectionalCurvature := by
    intro s hs y a b
    exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hoperator s (lt_of_le_of_lt hs.2 ht) y) a b
  have hspace := Splitting.ricciNullity_eq_on_positive_slice hC (by linarith : t - 1 < t)
    G hsec (show t ∈ Ioc (t - 1) t by constructor <;> linarith) x p
  change Splitting.ricciNullity (F.connection t) x =
    Splitting.ricciNullity (F.connection t) p at hspace
  by_contra hpos
  have hzero : (F.connection t).scalarCurvature x = 0 :=
    le_antisymm (le_of_not_gt hpos)
      ((Real.sqrt_nonneg _).trans
        ((F.connection t).curvatureTensorNorm_le_scalarCurvature_sharp hD x (hoperator t ht x)))
  have hRic (v : TangentSpace (𝓡 3) x) : (F.connection t).ricci x v v = 0 := by
    have h := (F.connection t).ricci_bounds_of_nonnegative_curvatureOperator hD x
      (hoperator t ht x) v
    rw [hzero, zero_mul] at h
    exact le_antisymm h.2 h.1
  have hkernel : Splitting.ricciKernel (F.connection t) x = ⊤ := by
    apply top_unique
    intro v _
    apply (Splitting.mem_ricciKernel _ _ _).mpr
    exact Splitting.ricci_eq_zero_of_nonneg_of_self_eq_zero (F.connection t) hD x
      (fun w => (hRic w).ge) (hRic v)
  have hdim : Splitting.ricciNullity (F.connection t) x = 3 := by
    unfold Splitting.ricciNullity
    rw [hkernel]
    simp [TangentSpace]
  omega

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem scalarCurvature_pos (hC : RicciFlowCurvatureTheory.{u})
    (L : AncientAsymptoticSolitonLimitData S) (t : ℝ) (ht : t < 0)
    (x : L.convergence.limit.carrier.carrier) :
    0 < (L.convergence.limit.flow.connection t).scalarCurvature x := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let : ConnectedSpace (ULift.{u} L.convergence.limit.carrier.carrier) :=
    Homeomorph.ulift.connectedSpace_iff.mpr inferInstance
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ULift.{u} L.convergence.limit.carrier.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ L.convergence.limit.carrier.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.convergence.limit.carrier.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) L.convergence.limit.carrier.carrier
  let F := L.convergence.limit.flow
  let G : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  have hop (s : ℝ) (hs : s < 0) (y : ULift.{u} L.convergence.limit.carrier.carrier) :
      (G.connection s).NonnegativeCurvatureOperator y :=
    (F.ulift_nonnegativeCurvatureOperator_iff s y).mpr
      (L.convergence.limit.nonnegative_curvature_operator s hs y.down)
  have hn : ∃ p, (G.connection t).curvatureTensorNorm p ≠ 0 := by
    obtain ⟨p, hp⟩ := L.nonflat_at t ht
    exact ⟨ULift.up p, by simpa only [G, F.ulift_curvatureTensorNorm] using hp⟩
  simpa only [G, F.ulift_scalarCurvature] using
    G.scalarCurvature_pos_of_nonflat_ancient_slice hC hop ht hn (ULift.up x)

end PoincareConjecture.AncientAsymptoticSolitonLimitData
