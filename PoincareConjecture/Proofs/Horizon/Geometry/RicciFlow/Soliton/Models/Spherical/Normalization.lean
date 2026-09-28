import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Spherical.FlowScale
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.CompactRoundShrinkingModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem round_of_metric_eq {g h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (hc : ConstantPositiveSectionalCurvature g D) :
    ConstantPositiveSectionalCurvature h D' := by
  subst h
  obtain ⟨c, hc, hsec⟩ := hc
  refine ⟨c, hc, fun x u v hu hv huv => ?_⟩
  have heq : D'.sectionalCurvature x u v = D.sectionalCurvature x u v := by
    simp only [LeviCivitaData.sectionalCurvature, D'.horizon_curvatureTensor_eq D]
  rw [heq]
  exact hsec x u v hu hv huv


theorem soliton_round (C : CompactRoundShrinkingModel G) :
    ConstantPositiveSectionalCurvature S.metric S.connection :=
  round_of_metric_eq (G.flow.connection (-1)) S.connection G.at_minus_one
    (C.round_at_time (-1) (by norm_num))


theorem soliton_sectionalCurvature (C : CompactRoundShrinkingModel G)
    (x : M) (u v : TangentSpace (𝓡 3) x)
    (hgram : S.metric.inner x u u * S.metric.inner x v v -
      (S.metric.inner x u v) ^ 2 ≠ 0) :
    S.connection.sectionalCurvature x u v = (1 / 4 : ℝ) := by
  let : CompactSpace M := C.compact
  obtain ⟨c, _, hsec⟩ := C.soliton_round
  have hall (y : M) (a b : TangentSpace (𝓡 3) y)
      (hab : S.metric.inner y a a * S.metric.inner y b b -
        (S.metric.inner y a b) ^ 2 ≠ 0) :
      S.connection.sectionalCurvature y a b = c :=
    S.connection.sectionalCurvature_eq_of_orthonormal y c (hsec y) a b hab
  have hRic (y : M) (a b : TangentSpace (𝓡 3) y) :
      S.connection.ricci y a b = 2 * c * S.metric.inner y a b := by
    have h := S.connection.ricci_of_constant_sectional y c (hall y) a b
    norm_num at h
    exact h
  have hunit (y : M) : ∃ a : TangentSpace (𝓡 3) y, S.metric.inner y a a = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨S.metric.toRiemannianMetric⟩
    let i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) y)) := ⟨0, by simp [TangentSpace]⟩
    refine ⟨S.metric.orthonormalBasis y i, ?_⟩
    change inner ℝ (S.metric.orthonormalBasis y i) (S.metric.orthonormalBasis y i) = 1
    simp
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    S.potential_C2.continuous.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    S.potential_C2.continuous.continuousOn
  obtain ⟨a, ha⟩ := hunit p
  obtain ⟨b, hb⟩ := hunit q
  have hmax := S.connection.hessian_nonpos_of_isLocalMax_C2 S.potential_C2
    (hp.isLocalMax (by simp)) a
  have hmin := S.connection.hessian_nonneg_of_isLocalMin_C2 S.potential_C2
    (hq.isLocalMin (by simp)) b
  have hsolmax := S.soliton_equation p a a
  have hsolmin := S.soliton_equation q b b
  rw [hRic, ha] at hsolmax
  rw [hRic, hb] at hsolmin
  have hc : c = (1 / 4 : ℝ) := by linarith
  rw [hall x u v hgram, hc]


theorem soliton_ricci (C : CompactRoundShrinkingModel G)
    (x : M) (u v : TangentSpace (𝓡 3) x) :
    S.connection.ricci x u v = (1 / 2 : ℝ) * S.metric.inner x u v := by
  have h := S.connection.ricci_of_constant_sectional x (1 / 4)
    (C.soliton_sectionalCurvature x) u v
  norm_num at h
  exact h


theorem inner_eq_neg_time_mul (C : CompactRoundShrinkingModel G)
    (t : ℝ) (ht : t < 0) (x : M) (u v : TangentSpace (𝓡 3) x) :
    (G.flow.metric t).inner x u v = (-t) * S.metric.inner x u v :=
  G.inner_eq_neg_time_mul_of_einstein C.soliton_ricci t ht x u v

end PoincareConjecture.CompactRoundShrinkingModel
