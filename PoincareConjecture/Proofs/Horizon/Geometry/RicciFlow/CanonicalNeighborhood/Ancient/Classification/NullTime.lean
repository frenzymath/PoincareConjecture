import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Product
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.UniversalCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.NullPersistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Component













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem exists_terminal_null_plane_of_null_plane
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) {b : ℝ} (hb : b ≤ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric b).inner x v v = 1)
    (hw : (K.flow.metric b).inner x w w = 1)
    (hvw : (K.flow.metric b).inner x v w = 0)
    (hzero : (K.flow.connection b).curvatureTensor x v w v w = 0) :
    ∃ (y : M) (a c : TangentSpace (𝓡 3) y),
      (K.flow.metric 0).inner y a a = 1 ∧ (K.flow.metric 0).inner y c c = 1 ∧
      (K.flow.metric 0).inner y a c = 0 ∧
      (K.flow.connection 0).curvatureTensor y a c a c = 0 := by
  obtain ⟨N, hN, hT, hconn, hm, hborel, hchart, hman, hsecond, hsimple,
    L, p, _, hsurj, _, hp, hmetric⟩ := K.exists_simplyConnected_covering_solution
  obtain ⟨y, rfl⟩ := hsurj x
  let D := hp.mfderivToContinuousLinearEquiv (by simp) y
  let v' := D.symm v
  let w' := D.symm w
  have hv' : mfderiv (𝓡 3) (𝓡 3) p y v' = v := D.apply_symm_apply v
  have hw' : mfderiv (𝓡 3) (𝓡 3) p y w' = w := D.apply_symm_apply w
  have hunitv : (L.flow.metric b).inner y v' v' = 1 := by rw [hmetric, hv']; exact hv
  have hunitw : (L.flow.metric b).inner y w' w' = 1 := by rw [hmetric, hw']; exact hw
  have horth : (L.flow.metric b).inner y v' w' = 0 := by rw [hmetric, hv', hw']; exact hvw
  have hnull : (L.flow.connection b).curvatureTensor y v' w' v' w' = 0 := by
    rw [(L.flow.connection b).curvatureTensor_eq_of_local_isometry (K.flow.connection b)
      isOpen_univ hp.contMDiff.contMDiffOn (fun z _ => hmetric b z) (mem_univ y), hv', hw']
    exact hzero
  obtain ⟨A⟩ := P.normalization N L y b hb
  let a := (Real.sqrt A.scale)⁻¹ • v'
  let c := (Real.sqrt A.scale)⁻¹ • w'
  have ha : (A.target.flow.metric 0).inner y a a = 1 :=
    (A.terminalNormalized_inner y v' v').trans hunitv
  have hc : (A.target.flow.metric 0).inner y c c = 1 :=
    (A.terminalNormalized_inner y w' w').trans hunitw
  have hac : (A.target.flow.metric 0).inner y a c = 0 :=
    (A.terminalNormalized_inner y v' w').trans horth
  have hz : (A.target.flow.connection 0).curvatureTensor y a c a c = 0 := by
    have heq := A.terminalNormalized_sectional y v' w'
    change (A.target.flow.connection 0).sectionalCurvature y a c = _ at heq
    simpa only [LeviCivitaData.sectionalCurvature, ha, hc, hac, hnull,
      zero_div, one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using heq
  obtain ⟨S, hS, hST, hSconn, hSm, hSb, hSchart, hSman, hSsecond, B, ⟨R⟩, e, _⟩ :=
    A.target.exists_compact_round_product_of_terminal_null P y a c ha hc hac hz
  let : CompactSpace S := R.compact
  exact (L.flow.metric 0).exists_null_plane_of_compact_prod_real_local_isometry
    e.toHomeomorph (L.flow.connection 0) (L.complete 0 le_rfl)
    (K.flow.metric 0) (K.flow.connection 0) hp.contMDiff (hmetric 0)
    (fun z v w => (K.flow.connection 0).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      z (K.nonnegative_curvature_operator 0 le_rfl z) v w)

end PoincareConjecture.AncientKappaSolution
