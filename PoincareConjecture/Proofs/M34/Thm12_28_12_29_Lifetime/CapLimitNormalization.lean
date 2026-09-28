import PoincareConjecture.Proofs.M34.Standard.CapIsometry
import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Definitions.M27CanonicalGeometry
import PoincareConjecture.Definitions.M30ControlledBlowupLimits

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

theorem sectional_nonneg_of_nonnegative_operator
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (hD : D.NonnegativeCurvatureOperator x) (v w : TangentSpace (𝓡 n) x) :
    0 ≤ D.curvatureTensor x v w v w := by
  have hA : IsSkewCoefficient 2 ![![0, 1], ![-1, 0]] := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hh := D.curvatureOperator_nonneg_in_frame x hD ![v, w] _ hA
  norm_num [Fin.sum_univ_two] at hh
  have hfirst := M04.curvatureTensor_swap_first D x w v v w
  have hlast := M04.curvatureTensor_swap_last D x v w w v
  have hboth := M04.curvatureTensor_swap_first D x w v w v
  linarith

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.M34

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    MeasurableSpace L.carrier.carrier := L.carrier.measurableSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    BorelSpace L.carrier.carrier := L.carrier.borelSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    T2Space L.carrier.carrier := L.carrier.t2Space
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    T3Space L.carrier.carrier := L.carrier.t3Space
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    SecondCountableTopology L.carrier.carrier := L.carrier.secondCountable
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ConnectedSpace L.carrier.carrier := L.connectedSpace

theorem blowupLimit_zero_geometry {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    MetricComplete (L.flow.metric 0) ∧
      (∀ x : L.carrier.carrier, ∀ v : TangentSpace (𝓡 3) x,
        0 ≤ (L.flow.connection 0).ricci x v v) ∧
      (L.flow.connection 0).scalarCurvature L.base = 1 := by
  refine ⟨L.complete 0 L.zero_mem, ?_, L.scalar_normalized⟩
  intro x v
  exact M04.nonneg_ricci_of_nonnegativeSectionalAt (L.flow.connection 0) x
    ((L.flow.connection 0).sectional_nonneg_of_nonnegative_operator x
      (L.nonnegative_curvature_operator 0 L.zero_mem x)) v

theorem exists_normalized_limit_cap_of_ancient
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) {kappa delta C : ℝ}
    (A : M30AncientKappaIdentification L kappa)
    (N : M27CanonicalCap A.certificate.solution 0 L.base delta C) :
    ∃ H : CapCertificate (L.flow.metric 0), H.epsilon = delta ∧ H.cap_constant ≤ C ∧
      H.connection = L.flow.connection 0 ∧ L.base ∈ H.core := by
  let f := Diffeomorph.refl (𝓡 3) L.carrier.carrier ∞
  have hf : MetricHomothety (A.certificate.solution.flow.metric 0)
      (L.flow.metric 0) f 1 := by
    intro x v w
    change (L.flow.metric 0).inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
      (mfderiv (𝓡 3) (𝓡 3) id x w) = _
    rw [mfderiv_id]
    simp only [ContinuousLinearMap.id_apply, one_mul, A.certificate.metric_eq 0 le_rfl]
  obtain ⟨H, hepsilon, hC, hD, hcore, _⟩ :=
    N.cap.exists_isometric_image_cap f hf (L.flow.connection 0)
  refine ⟨H, hepsilon.trans N.epsilon_eq, hC.trans_le N.constant_le, hD, ?_⟩
  rw [hcore]
  exact ⟨L.base, N.contains, rfl⟩

end PoincareConjecture.M34
