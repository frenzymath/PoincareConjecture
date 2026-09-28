import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientHomothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciPropagation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.CurvatureNullity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M}

theorem ShrinkingSolitonFlow.nonnegativeSectionalCurvature
    (G : ShrinkingSolitonFlow S) {t : ℝ} (ht : t < 0) :
    (G.flow.connection t).NonnegativeSectionalCurvature := by
  obtain ⟨E⟩ := G.self_similar t ht
  intro x v w
  rw [(G.flow.connection t).curvatureTensor_eq_of_local_isometry
    (rescaledMetric_connection S.metric S.connection |t| (abs_pos.mpr ht.ne))
    isOpen_univ E.map.contMDiff.contMDiffOn
    (fun y _ a b => E.inner_eq y a b) (mem_univ x), rescaledMetric_curvatureTensor]
  exact mul_nonneg (abs_nonneg t)
    (S.connection.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      _ (S.nonnegative_curvature _) _ _)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem ricci_eq_of_metric_eq {g h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (x : M) (v w : TangentSpace (𝓡 3) x) : D.ricci x v w = D'.ricci x v w := by
  subst h
  simp only [LeviCivitaData.ricci, D.horizon_curvatureTensor_eq D']

theorem ShrinkingSolitonFlow.ricci_pos_of_compact [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (G : ShrinkingSolitonFlow S)
    (x : M) (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0) :
    0 < S.connection.ricci x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    S.potential_C2.continuous.continuousOn
  have hpRic (z : TangentSpace (𝓡 3) p) (hz : z ≠ 0) :
      0 < S.connection.ricci p z z := by
    have hmax := S.connection.hessian_nonpos_of_isLocalMax_C2 S.potential_C2
      (hp.isLocalMax (by simp)) z
    have hs := S.soliton_equation p z z
    have hnorm : 0 < S.metric.inner p z z := real_inner_self_pos.mpr hz
    linarith
  have hsame (y : M) (a b : TangentSpace (𝓡 3) y) :
      (G.flow.connection (-1)).ricci y a b = S.connection.ricci y a b :=
    ricci_eq_of_metric_eq _ _ G.at_minus_one y a b
  have hker : RicciFlow.Splitting.ricciKernel (G.flow.connection (-1)) p = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    by_contra hzero
    have hz' := (RicciFlow.Splitting.mem_ricciKernel _ _ _).mp hz z
    rw [hsame] at hz'
    exact (hpRic z hzero).ne' hz'
  have hpdim : RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) p = 0 := by
    simp [RicciFlow.Splitting.ricciNullity, hker]
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (show Icc (-2 : ℝ) (-1) ⊆ Iio 0 from fun _ hs => lt_of_le_of_lt hs.2 (by norm_num))
    ordConnected_Icc ⟨-2, by simp, -1, by simp, by norm_num⟩
  have hdim := RicciFlow.Splitting.ricciNullity_eq_on_positive_slice hC
    (by norm_num : (-2 : ℝ) < -1) F
    (fun t ht => G.nonnegativeSectionalCurvature (lt_of_le_of_lt ht.2 (by norm_num)))
    (show (-1 : ℝ) ∈ Ioc (-2) (-1) by norm_num) x p
  change RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) x =
    RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) p at hdim
  rw [hpdim] at hdim
  have hD := hC.tensor_calculus 3 M S.metric S.connection
  have hnonneg (z : TangentSpace (𝓡 3) x) : 0 ≤ S.connection.ricci x z z :=
    (S.connection.ricci_bounds_of_nonnegative_curvatureOperator hD x
      (S.nonnegative_curvature x) z).1
  by_contra hpos
  have hzero : S.connection.ricci x v v = 0 :=
    le_antisymm (le_of_not_gt hpos) (hnonneg v)
  have hvker : v ∈ RicciFlow.Splitting.ricciKernel (G.flow.connection (-1)) x := by
    apply (RicciFlow.Splitting.mem_ricciKernel _ _ _).mpr
    intro w
    rw [hsame]
    exact RicciFlow.Splitting.ricci_eq_zero_of_nonneg_of_self_eq_zero
      S.connection hD x hnonneg hzero w
  have hdimpos : 0 < RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) x := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, hvker⟩, fun h => hv (congrArg Subtype.val h)⟩
  omega

end PoincareConjecture
