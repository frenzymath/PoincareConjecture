import PoincareConjecture.Proofs.M45.Ch9_Models.FiniteGradient
import PoincareConjecture.Proofs.M45.Ch9_Models.NormalizedChart
import PoincareConjecture.Proofs.M45.Ch9_Models.MetricRealization
import PoincareConjecture.Proofs.M45.Ch9_Models.NeckBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundFourJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundActualScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

open PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem exists_model_round_analytic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M],
      ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (epsilon : ℝ)
        (R : SingularRoundComponent g epsilon), epsilon ≤ 1 / 200 →
        ∀ x ∈ R.carrier, M45PointwiseAnalyticEstimate g D x C := by
  obtain ⟨B, _, hB⟩ := exists_round_comparison_coordinate_bounds
  obtain ⟨Cg, hCg, hgradient⟩ :=
    exists_model_scalar_differential_bound_of_coordinate_jets B
  obtain ⟨Ce, hCe, hevolution⟩ := exists_scalar_evolution_bound_of_coordinate_jets 3
    (show (0 : ℝ) < 1 / 2 by norm_num) B
  refine ⟨max Cg Ce, lt_of_lt_of_le hCg (le_max_left _ _), ?_⟩
  intro M _ _ _ g D epsilon R hsmall x hx
  obtain ⟨_, horder⟩ := model_four_jet_order R.epsilon_pos hsmall
  obtain ⟨f, V, gB, DB, hfzero, hV, hzeroV, hf, hinv, hcurv, hgram, hactual⟩ :=
    hB R (by linarith) horder (R.inverse x)
  have hfzero' : f 0 = x := hfzero.trans (R.right_inverse hx)
  obtain ⟨gE, DE, W, hW, hzeroW, hWV, hmetric⟩ :=
    model_metric_realization g hV hzeroV hf hinv
  let gQ := m01RescaledMetric gE R.scale R.scale_pos
  let DQ := m01RescaledMetric_connection gE DE R.scale R.scale_pos
  have hcoeff : gQ.euclideanCoefficients =ᶠ[𝓝 0]
      (fun y => R.scale • g.pullbackCoefficients f y) := by
    filter_upwards [hW.mem_nhds hzeroW] with y hy
    exact congrArg (fun B => R.scale • B) (hmetric y hy)
  obtain ⟨hfour, hell, herror⟩ := hactual gQ hcoeff
  have hpositive := scalarCurvature_three_le_of_round_metric_error DB DQ 0
    R.epsilon_pos.le hsmall hcurv hgram (fun j hj => herror j (by omega))
  have hgeom (y : E) (hy : y ∈ W) (v w : E) :
      gE.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun B => B v w) (hmetric y hy)
  have hscale : DQ.scalarCurvature 0 = DE.scalarCurvature 0 / R.scale :=
    M13.homothety_scalarCurvature_eq gE gQ (Diffeomorph.refl (𝓡 3) E ∞)
      R.scale R.scale_pos (rescaledMetric_identity_homothety R.scale_pos) DE DQ 0
  rw [hscale, DE.scalarCurvature_eq_of_local_isometry D hW (hf.mono hWV) hgeom hzeroW]
    at hpositive
  have hscalar : R.scale ≤ D.scalarCurvature (f 0) := by
    have h := (le_div_iff₀ R.scale_pos).mp hpositive
    linarith [R.scale_pos]
  have h := model_analytic_of_normalized_chart D gE DE R.scale_pos hCg hCe hW hzeroW
    (hf.mono hWV) (fun y hy => hinv y (hWV hy)) hgeom hscalar
    (hgradient gQ DQ 0 hfour hell) (hevolution gQ DQ 0 hfour hell)
  simpa only [hfzero'] using h

end PoincareConjecture.M45
