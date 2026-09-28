import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem scalarDerivatives_round_contractions
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (hround : IsRoundMetricSlice D) :
    ∃ r : ℝ, 0 < r ∧ (∀ x, D.scalarCurvature x = 6 * r) ∧
      ∀ x, ∀ v w : TangentSpace (𝓡 3) x, D.ricci x v w = 2 * r * g.inner x v w := by
  obtain ⟨r, hr, hcurv⟩ := hround
  have hsec (x : M) (v w : TangentSpace (𝓡 3) x)
      (hgram : g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0) :
      D.sectionalCurvature x v w = r := by
    unfold LeviCivitaData.sectionalCurvature
    rw [hcurv]
    exact mul_div_cancel_right₀ r hgram
  refine ⟨r, hr, fun x => ?_, fun x v w => ?_⟩
  · convert D.scalarCurvature_of_constant_sectional x r (hsec x) using 1
    norm_num
  · convert D.ricci_of_constant_sectional x r (hsec x) v w using 1
    norm_num

theorem round_scalarGradientNorm_eq_zero
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hround : IsRoundMetricSlice D) (x : M) : scalarGradientNorm g D x = 0 := by
  obtain ⟨r, _, hscalar, _⟩ := scalarDerivatives_round_contractions D hround
  have heq : D.scalarCurvature = fun _ => 6 * r := funext hscalar
  unfold scalarGradientNorm
  rw [heq]
  simp only [mvfderiv_const]
  rcases isEmpty_or_nonempty {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} with h | h
  · rw [Set.range_eq_empty_iff.mpr h]
    exact Real.sSup_empty
  · simp

theorem round_scalarEvolution_bound
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hround : IsRoundMetricSlice D) (x : M) :
    |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤
      2 * D.scalarCurvature x ^ 2 := by
  obtain ⟨r, hr, hscalar, hric⟩ := scalarDerivatives_round_contractions D hround
  have heq : D.scalarCurvature = fun _ => 6 * r := funext hscalar
  have hlap : D.laplacian D.scalarCurvature x = 0 := by
    rw [heq]
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  have hRic : ∀ v : TangentSpace (𝓡 3) x, 0 ≤ D.ricci x v v := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    intro v
    rw [hric]
    change 0 ≤ 2 * r * inner ℝ v v
    exact mul_nonneg (by positivity) real_inner_self_nonneg
  have hnorm := D.ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg hD x hRic
  have hnorm0 : 0 ≤ D.ricciNormSq x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hlap, zero_add, abs_of_nonneg (mul_nonneg (by norm_num) hnorm0)]
  linarith

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem round_scalarDerivWithin_bound
    (S : ScalarDerivativeServices.{u}) (K : AncientKappaSolution 3 M)
    (hround : IsRoundAncientKappaSolution K) {t : ℝ} (ht : t ≤ 0) (x : M) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
        d (Set.Iic 0) t ∧
      |d| ≤ 2 * (K.flow.connection t).scalarCurvature x ^ 2 := by
  refine ⟨_, S.scalar_evolution M (Set.Iic 0) K.flow t ht x, ?_⟩
  exact round_scalarEvolution_bound (K.flow.connection t)
    (S.tensor_calculus 3 M (K.flow.metric t) (K.flow.connection t)) (hround t ht) x

end PoincareConjecture
