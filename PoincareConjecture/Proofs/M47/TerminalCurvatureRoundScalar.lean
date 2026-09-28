import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundFourJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundActualScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling
import PoincareConjecture.Proofs.M45.Ch9_Models.MetricRealization
import PoincareConjecture.Proofs.M45.Ch9_Models.NeckBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_scalar_le_of_round_error {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hcurv : D.curvatureTensorNorm x ≤ 9)
    (hgram : ∀ u v : E, D.curvatureTensor x u v u v =
      g.inner x u u * g.inner x v v - g.inner x u v ^ 2)
    (herror : ∀ j ≤ 2,
      g.tensorNorm (D.iteratedCovariantTensorDerivative (M44.metricError g h) j) x ≤ epsilon) :
    D'.scalarCurvature x ≤ 72 := by
  have hmetric (u v : E) : |h.inner x u v - g.inner x u v| ≤
      epsilon * (g.tangentNorm x u * g.tangentNorm x v) := by
    simpa! only [Nat.add_zero, LeviCivitaData.iteratedCovariantTensorDerivative,
      M44.metricError, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      M44.metricError_jet_evaluation_le D 0 x (herror 0 (by omega)) ![u, v]
  have hpos (v : E) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hquad (v : E) : g.tangentNorm x v ^ 2 = g.inner x v v :=
    Real.sq_sqrt (hpos v)
  have hplane (u v : E) : |D'.curvatureTensor x u v u v -
      (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)| ≤
        13 * epsilon * (g.inner x u u * g.inner x v v) := by
    have hh := M44.abs_curvatureTensor_difference_le D D' x hepsilon
      (show epsilon ≤ 1 / 4 by linarith) hcurv herror u v u v
    rw [hgram] at hh
    have hp : g.tangentNorm x u * g.tangentNorm x v *
        g.tangentNorm x u * g.tangentNorm x v = g.inner x u u * g.inner x v v := by
      rw [← hquad, ← hquad]
      ring
    rw [hp] at hh
    have hcoeff : (9 + 3 : ℝ) * epsilon + 10 * epsilon ^ 2 ≤ 13 * epsilon := by
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (hpos u) (hpos v)))
  have hunit (v : E) (hv : h.inner x v v = 1) : g.inner x v v ≤ 2 := by
    have he := hmetric v v
    rw [hv, ← sq, hquad] at he
    have heps : epsilon * g.inner x v v ≤ (1 / 2 : ℝ) * g.inner x v v :=
      mul_le_mul_of_nonneg_right (by linarith) (hpos v)
    linarith [(abs_le.mp he).1]
  have hterm (u v : E) (hu : h.inner x u u = 1) (hv : h.inner x v v = 1) :
      D'.curvatureTensor x u v u v ≤ 8 := by
    have hprod : g.inner x u u * g.inner x v v ≤ 4 := by
      nlinarith [mul_le_mul (hunit u hu) (hunit v hv) (hpos v) (by norm_num : (0 : ℝ) ≤ 2)]
    have hcoeff : 13 * epsilon ≤ 1 := by linarith
    have herr := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (hpos u) (hpos v))
    have hp := (abs_le.mp (hplane u v)).2
    nlinarith [sq_nonneg (g.inner x u v)]
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := h.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    simp [TangentSpace]
  have hb (i) : h.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    simp
  calc
    D'.scalarCurvature x = ∑ i, ∑ j, D'.curvatureTensor x (b i) (b j) (b i) (b j) := rfl
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)), (8 : ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm _ _ (hb i) (hb j)
    _ = 72 := by norm_num [hdim]



theorem terminalCurvature_round_scalar_upper
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {epsilon : ℝ} (N : SingularRoundComponent g epsilon) (hsmall : epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) : D.scalarCurvature x ≤ 72 * N.scale := by
  obtain ⟨_, _, hB⟩ := M44.exists_round_comparison_coordinate_bounds
  obtain ⟨_, horder⟩ := M45.model_four_jet_order N.epsilon_pos hsmall
  obtain ⟨f, V, gB, DB, hfzero, hV, hzeroV, hf, hinv, hcurv, hgram, hactual⟩ :=
    hB N (by linarith) horder (N.inverse x)
  have hfzero' : f 0 = x := hfzero.trans (N.right_inverse hx)
  obtain ⟨gE, DE, W, hW, hzeroW, hWV, hmetric⟩ :=
    M45.model_metric_realization g hV hzeroV hf hinv
  let gQ := m01RescaledMetric gE N.scale N.scale_pos
  let DQ := m01RescaledMetric_connection gE DE N.scale N.scale_pos
  have hcoeff : gQ.euclideanCoefficients =ᶠ[𝓝 0]
      (fun y => N.scale • g.pullbackCoefficients f y) := by
    filter_upwards [hW.mem_nhds hzeroW] with y hy
    exact congrArg (fun B => N.scale • B) (hmetric y hy)
  obtain ⟨_, _, herror⟩ := hactual gQ hcoeff
  have hupper := terminalCurvature_scalar_le_of_round_error DB DQ 0 N.epsilon_pos.le
    hsmall hcurv hgram (fun j hj => herror j (by omega))
  have hgeom (y : E) (hy : y ∈ W) (v w : E) :
      gE.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun B => B v w) (hmetric y hy)
  have hscale : DQ.scalarCurvature 0 = DE.scalarCurvature 0 / N.scale :=
    M13.homothety_scalarCurvature_eq gE gQ (Diffeomorph.refl (𝓡 3) E ∞)
      N.scale N.scale_pos (M44.rescaledMetric_identity_homothety N.scale_pos) DE DQ 0
  rw [hscale, DE.scalarCurvature_eq_of_local_isometry D hW (hf.mono hWV) hgeom hzeroW,
    hfzero'] at hupper
  exact (div_le_iff₀ N.scale_pos).mp hupper

end PoincareConjecture.M47
