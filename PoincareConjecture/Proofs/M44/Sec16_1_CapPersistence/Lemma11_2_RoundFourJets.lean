import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundErrorJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)





theorem exists_round_comparison_coordinate_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
        {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon),
        epsilon ≤ 1 / 2 → 4 ≤ ⌊epsilon⁻¹⌋₊ → ∀ p : R.model.carrier,
        ∃ (f : E → X) (V : Set E) (gB : RiemannianMetric 3 E) (DB : LeviCivitaData gB),
          f 0 = R.forward p ∧ IsOpen V ∧ (0 : E) ∈ V ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V ∧
          (∀ y ∈ V, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) ∧
          DB.curvatureTensorNorm 0 ≤ 9 ∧
          (∀ u v : E, DB.curvatureTensor 0 u v u v =
            gB.inner 0 u u * gB.inner 0 v v - gB.inner 0 u v ^ 2) ∧
          ∀ gE : RiemannianMetric 3 E,
            gE.euclideanCoefficients =ᶠ[𝓝 0]
              (fun y => R.scale • g.pullbackCoefficients f y) →
            (∀ j ≤ 4, ‖iteratedFDeriv ℝ j gE.euclideanCoefficients 0‖ ≤ C) ∧
              (∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gE.inner 0 v v) ∧
              ∀ j ≤ 4, gB.tensorNorm (DB.iteratedCovariantTensorDerivative (k := 2)
                (fun y v => gE.inner y (v 0) (v 1) - gB.inner y (v 0) (v 1)) j) 0 ≤
                  epsilon := by
  obtain ⟨r, hr, B, hB, hmodel⟩ := exists_round_model_coordinate_bounds
  let B0 : ℝ := 1 + ∑ j : Fin 6, B j
  have hB0 (j : ℕ) (hj : j ≤ 5) : B j ≤ B0 := by
    have h := Finset.single_le_sum (f := fun l : Fin 6 => B l) (fun l _ => hB l)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin 6))
    dsimp [B0]
    linarith
  choose A hA hbound using fun j : Fin 5 => exists_uniform_bilinear_error_jet_bound j
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num) B0
  let C : ℝ := 1 + ∑ j : Fin 5, (A j + B j)
  have hsum : 0 ≤ ∑ j : Fin 5, (A j + B j) :=
    Finset.sum_nonneg fun j _ => add_nonneg (hA j).le (hB j)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro X _ _ _ g epsilon R hsmall horder p
  obtain ⟨e, he0, he, hinv, hnorm, _, hjets⟩ :=
    hmodel R.model_metric R.model_connection R.model_compact R.model_curvature_one p
  have hzero : (0 : E) ∈ Metric.ball 0 (2 * r) := Metric.mem_ball_self (by positivity)
  have hcoeff : ContDiffOn ℝ ∞ (R.model_metric.pullbackCoefficients e)
      (Metric.ball 0 (2 * r)) := fun x hx =>
    (R.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx))).contDiffWithinAt
  obtain ⟨gB, DB, V, hV, h0V, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization Metric.isOpen_ball hzero
      (R.model_metric.pullbackCoefficients e) hcoeff
      (fun x _ v w => R.model_metric.symm (e x) _ _)
      (fun x hx v hv => by
        apply R.model_metric.pos (e x)
        intro hz
        apply hv
        apply (hinv x hx).injective
        rw [map_zero]
        convert! hz using 1)
  have hgerm : gB.euclideanCoefficients =ᶠ[𝓝 0] R.model_metric.pullbackCoefficients e :=
    eventually_of_mem (hV.mem_nhds h0V) hmetric
  have hinner (v w : E) : gB.inner 0 v w = inner ℝ v w :=
    (congrArg (fun H => H v w) hgerm.self_of_nhds).trans (hnorm v w)
  have hbase (j : ℕ) : ‖iteratedFDeriv ℝ j gB.euclideanCoefficients 0‖ ≤ B j := by
    rw [(hgerm.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
    exact hjets j 0 (Metric.mem_closedBall_self hr.le)
  have hframe (b : Fin 3) :
      gB.tangentNorm 0 (EuclideanSpace.basisFun (Fin 3) ℝ b) ≤ 1 := by
    simp only [RiemannianMetric.tangentNorm, hinner, real_inner_self_eq_norm_sq,
      OrthonormalBasis.norm_eq_one, one_pow, Real.sqrt_one, le_refl]
  let f : E → X := R.forward ∘ e
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 (2 * r)) :=
    R.forward_smooth.comp_contMDiffOn he
  have he0smooth := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hzero)
  have heinv : ∀ᶠ y in 𝓝 (0 : E), (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hzero) hinv
  have hgeometric : ∀ᶠ y in 𝓝 (0 : E), ∀ u v : E,
      gB.inner y u v = R.model_metric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y u) (mfderiv (𝓡 3) (𝓡 3) e y v) :=
    hgerm.mono fun y hy u v => congrArg (fun H => H u v) hy
  have hcurv : DB.curvatureTensorNorm 0 ≤ 9 := by
    rw [DB.curvatureTensorNorm_eq_pullback_euclidean R.model_connection
      he0smooth heinv hgeometric]
    exact curvatureTensorNorm_le_nine_of_sectional_one R.model_connection
      R.model_curvature_one (e 0)
  have hgram (u v : E) : DB.curvatureTensor 0 u v u v =
      gB.inner 0 u u * gB.inner 0 v v - gB.inner 0 u v ^ 2 := by
    rw [DB.curvatureTensor_eq_pullback_euclidean R.model_connection
      he0smooth heinv hgeometric,
      curvatureTensor_eq_metricGram_of_sectional_one R.model_connection R.model_curvature_one]
    rw [← hgeometric.self_of_nhds u u, ← hgeometric.self_of_nhds v v,
      ← hgeometric.self_of_nhds v u, ← hgeometric.self_of_nhds u v, gB.symm 0 v u]
    ring
  refine ⟨f, V, gB, DB, by simp only [f, Function.comp_apply, he0],
    hV, h0V, hf.mono hVU, ?_, hcurv, hgram, ?_⟩
  · intro y hy
    exact round_composition_mfderiv_isInvertible R
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hVU hy))) (hinv y (hVU hy))
  intro gE hactual
  obtain ⟨W, hW, hWo, h0W⟩ := mem_nhds_iff.mp hactual
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hWo
  have h0U : (0 : E) ∈ U := ⟨h0V, h0W⟩
  have hsub : U ⊆ Metric.ball 0 (2 * r) := fun _ hx => hVU hx.1
  have hgeom (y : E) (hy : y ∈ U) (v w : E) :
      gB.inner y v w = R.model_metric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) :=
    congrArg (fun H => H v w) (hmetric y hy.1)
  have hchain (y : E) (hy : y ∈ Metric.ball 0 (2 * r)) :
      mfderiv (𝓡 3) (𝓡 3) f y =
        (mfderiv (𝓡 3) (𝓡 3) R.forward (e y)).comp (mfderiv (𝓡 3) (𝓡 3) e y) :=
    mfderiv_comp y (R.forward_smooth.mdifferentiable (by simp) (e y))
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hy)).mdifferentiableAt (by simp))
  have herror (m : ℕ) (hm : m ≤ 4) :
      gB.tensorNorm (DB.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => gE.euclideanCoefficients y (v 0) (v 1) -
          gB.inner y (v 0) (v 1)) m) 0 ≤ epsilon := by
    rw [local_bilinear_covariant_norm_eq_pullback DB R.model_connection hU
      (he.mono hsub) (fun y hy => hinv y (hsub hy)) hgeom
      (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients).contDiffOn
      (round_error_isSmooth R) (fun y hy v => ?_) m h0U]
    · exact (round_covariant_error_lt R (hm.trans horder) (e 0)).le
    · rw [hW hy.2]
      change R.scale * g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y (v 0)) (mfderiv (𝓡 3) (𝓡 3) f y (v 1)) -
        gB.inner y (v 0) (v 1) = _
      rw [hgeom y hy, hchain y (hsub hy)]
      rfl
  refine ⟨?_, ?_, herror⟩
  · intro j hj
    let k : Fin 5 := ⟨j, by omega⟩
    have hb := hbound k DB gE.euclideanCoefficients U hU
      (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients).contDiffOn
      epsilon R.epsilon_pos.le 0 h0U
      (fun v => by rw [hinner, real_inner_self_eq_norm_sq, one_mul])
      (fun m hm => (hbase m).trans (hB0 m (by dsimp [k] at hm; omega))) hframe
      (fun m hm => herror m (by dsimp [k] at hm; omega))
    have heq : gE.euclideanCoefficients =
        fun y => (gE.euclideanCoefficients - gB.euclideanCoefficients) y +
          gB.euclideanCoefficients y := by
      funext y
      ext v w
      simp
    have hder : iteratedFDeriv ℝ j gE.euclideanCoefficients 0 =
        iteratedFDeriv ℝ j (gE.euclideanCoefficients - gB.euclideanCoefficients) 0 +
          iteratedFDeriv ℝ j gB.euclideanCoefficients 0 := by
      conv_lhs => rw [heq]
      exact fun_iteratedFDeriv_add_apply
        (((gE.contDiffAt_euclideanCoefficients 0).sub
          (gB.contDiffAt_euclideanCoefficients 0)).of_le (by exact_mod_cast le_top))
        ((gB.contDiffAt_euclideanCoefficients 0).of_le (by exact_mod_cast le_top))
    rw [hder]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (gE.euclideanCoefficients - gB.euclideanCoefficients) 0‖ +
          ‖iteratedFDeriv ℝ j gB.euclideanCoefficients 0‖ := norm_add_le _ _
      _ ≤ A k * epsilon + B j := add_le_add hb (hbase j)
      _ ≤ A k + B j := by nlinarith [hA k]
      _ ≤ ∑ l : Fin 5, (A l + B l) :=
        Finset.single_le_sum (fun l _ => add_nonneg (hA l).le (hB l)) (Finset.mem_univ k)
      _ ≤ C := by dsimp [C]; linarith
  · intro v
    have h := (round_quadratic_bounds R (e 0) (mfderiv (𝓡 3) (𝓡 3) e 0 v)).1
    have heval : gE.inner 0 v v = R.scale * g.inner (f 0)
        (mfderiv (𝓡 3) (𝓡 3) R.forward (e 0) (mfderiv (𝓡 3) (𝓡 3) e 0 v))
        (mfderiv (𝓡 3) (𝓡 3) R.forward (e 0) (mfderiv (𝓡 3) (𝓡 3) e 0 v)) := by
      change gE.euclideanCoefficients 0 v v = _
      rw [hactual.self_of_nhds]
      change R.scale * g.inner (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 v)
        (mfderiv (𝓡 3) (𝓡 3) f 0 v) = _
      rw [hchain 0 hzero]
      rfl
    rw [← hgeom 0 h0U, hinner, real_inner_self_eq_norm_sq] at h
    rw [heval]
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ R.scale * g.inner (R.forward (e 0)) _ _
    nlinarith [sq_nonneg ‖v‖]




theorem exists_round_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
        {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon),
        epsilon ≤ 1 / 2 → 4 ≤ ⌊epsilon⁻¹⌋₊ → ∀ p : R.model.carrier,
        ∃ f : E → X, f 0 = R.forward p ∧ ContMDiffAt (𝓡 3) (𝓡 3) ∞ f 0 ∧
          ∀ gE : RiemannianMetric 3 E,
            gE.euclideanCoefficients =ᶠ[𝓝 0]
              (fun y => R.scale • g.pullbackCoefficients f y) →
            (∀ j ≤ 4, ‖iteratedFDeriv ℝ j gE.euclideanCoefficients 0‖ ≤ C) ∧
              ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ gE.inner 0 v v := by
  obtain ⟨C, hC, hbound⟩ := exists_round_comparison_coordinate_bounds
  refine ⟨C, hC, ?_⟩
  intro X _ _ _ g epsilon R hsmall horder p
  obtain ⟨f, V, gB, DB, hf0, hV, h0, hf, _, _, _, hjets⟩ := hbound R hsmall horder p
  exact ⟨f, hf0, hf.contMDiffAt (hV.mem_nhds h0), fun gE hE =>
    ⟨(hjets gE hE).1, (hjets gE hE).2.1⟩⟩

end PoincareConjecture.M44
