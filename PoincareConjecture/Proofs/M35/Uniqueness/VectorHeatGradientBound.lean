import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatQuadratic
import PoincareConjecture.Proofs.M35.Uniqueness.RawQuadraticBound
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem vector_heat_product_quadratic_bound {B q Q L : ℝ}
    (hB : 0 ≤ B) (hq : 0 ≤ q) (hqb : q ≤ B) (hQ : 0 ≤ Q) (hL : 0 ≤ L) :
    L * ((16 * B + 1 + q) * Q) - Q ^ 2 ≤
      -(1 / (2 * (17 * B + 1) ^ 2)) * ((16 * B + 1 + q) * Q) ^ 2 +
        (L * (17 * B + 1)) ^ 2 / 2 := by
  let C := 17 * B + 1
  let F := (16 * B + 1 + q) * Q
  have hC : 0 < C := by dsimp [C]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFC : F ≤ C * Q := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hQ
  have hLF := mul_le_mul_of_nonneg_left hFC hL
  have hsq := (sq_le_sq₀ hF (mul_nonneg hC.le hQ)).mpr hFC
  have hfrac : (1 / (2 * C ^ 2)) * F ^ 2 ≤ Q ^ 2 / 2 := by
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ (show 0 < 2 * C ^ 2 by positivity)).mpr
    nlinarith only [hsq]
  change L * F - Q ^ 2 ≤ -(1 / (2 * C ^ 2)) * F ^ 2 + (L * C) ^ 2 / 2
  nlinarith only [hLF, hfrac, sq_nonneg (Q - L * C)]




theorem bounded_vector_heat_gradient_weighted
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B a I : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B) (ha : 0 ≤ a) (hI : 0 ≤ I)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ))
    (hbound : ∀ t ∈ Icc 0 T, ∀ x,
      (G.flow.metric t).inner x (X t x) (X t x) ≤ B)
    (hinit : ∀ x, a * ((G.flow.metric 0).tensorNorm
      ((G.flow.connection 0).covariantTensorDerivative
        (killingCovector (G.flow.metric 0) (X 0))) x) ^ 2 ≤ I)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x,
      (a + t) * ((G.flow.metric t).tensorNorm
        ((G.flow.connection t).covariantTensorDerivative
          (killingCovector (G.flow.metric t) (X t))) x) ^ 2 ≤ C := by
  let α := fun s => killingCovector (G.flow.metric s) (X s)
  let H := fun s => (G.flow.connection s).covariantTensorDerivative (α s)
  let Q := fun s y => ((G.flow.metric s).tensorNorm (H s) y) ^ 2
  let q := fun s y => (G.flow.metric s).inner y (X s y) (X s y)
  let F := fun s y => (16 * B + 1 + q s y) * Q s y
  have hα (s : ℝ) : IsSmoothCovariantTensor (α s) :=
    isSmoothCovariantTensor_killingCovector _ _ (hX s)
  have hH (s : ℝ) : IsSmoothCovariantTensor (H s) :=
    M04.isSmoothCovariantTensor_covariantTensorDerivative _ (hα s)
  have hQjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry Q) (Ico 0 G.lifetime ×ˢ univ) := by
    apply M04.contMDiffOn_flow_tensorNorm_sq G.flow H hH
    intro U hU Y hY
    exact M04.contMDiffOn_flow_covariantTensorDerivative G.flow hα
      (killingCovector_joint G X hJoint) hU hY
  have hqjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry q) (Ico 0 G.lifetime ×ˢ univ) := by
    have hn := M04.contMDiffOn_flow_tensorNorm_sq G.flow α hα
      (killingCovector_joint G X hJoint)
    simpa only [α, killingCovector_normSq] using! hn
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have hFcont : ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) :=
    ((continuousOn_const.add hqjoint.continuousOn).mul hQjoint.continuousOn).mono
      (prod_mono hsub Subset.rfl)
  have hq (s : ℝ) (y : StandardCapSpace) : 0 ≤ q s y := by
    change 0 ≤ (G.flow.metric s).inner y (X s y) (X s y)
    rw [← killingCovector_normSq (G.flow.metric s) (X s) y]
    exact sq_nonneg _
  have hQ (s : ℝ) (y : StandardCapSpace) : 0 ≤ Q s y := sq_nonneg _
  have hF (s : ℝ) (y : StandardCapSpace) : 0 ≤ F s y := by
    have hq' := hq s y
    exact mul_nonneg (by positivity) (hQ s y)
  have hFC (s : ℝ) (hs : s ∈ Icc 0 T) (y : StandardCapSpace) :
      F s y ≤ (17 * B + 1) * Q s y := by
    apply mul_le_mul_of_nonneg_right _ (hQ s y)
    have hb := hbound s hs y
    change q s y ≤ B at hb
    linarith
  have hFinit (y : StandardCapSpace) : a * F 0 y ≤ (17 * B + 1) * I := by
    have hi : a * Q 0 y ≤ I := hinit y
    have hc := mul_le_mul_of_nonneg_left (hFC 0 ⟨le_rfl, hT.le⟩ y) ha
    have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 17 * B + 1 by positivity)
    nlinarith only [hc, hh]
  have hFs (s : ℝ) (_hs : s ∈ Ioc 0 T) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (F s) := by
    have hQs := M04.contMDiff_tensorNorm_sq (G.flow.metric s) (hH s)
    have hqs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (q s) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
        ⟨(G.flow.metric s).toRiemannianMetric⟩
      exact (euclidean_field_contMDiff (hX s)).inner_bundle
        (euclidean_field_contMDiff (hX s))
    exact (contMDiff_const.add hqs).mul hQs
  obtain ⟨K, hK, hRm⟩ := G.curvature_locally_bounded T hT.le hTlt
  let c := 1 / (2 * (17 * B + 1) ^ 2)
  let d := (324 * K * (17 * B + 1)) ^ 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hFd (s : ℝ) (hs : s ∈ Ioc 0 T) (y : StandardCapSpace) : ∃ z : ℝ,
      HasDerivWithinAt (fun r => F r y) z (Icc 0 s) s ∧
        z - (G.flow.connection s).laplacian (F s) y ≤ -c * F s y ^ 2 + d := by
    have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    obtain ⟨z, hz, hze⟩ := vector_heat_product_reaction G hT hTlt hs hK hB X hX hJoint
      (hheat s hs) y ((le_abs_self _).trans (hRm s hs' y)) (hbound s hs' y)
    refine ⟨z, hz.mono (fun r hr => ⟨hr.1, hr.2.trans hs.2⟩), hze.trans ?_⟩
    exact vector_heat_product_quadratic_bound hB (hq s y) (hbound s hs' y) (hQ s y)
      (mul_nonneg (by norm_num) hK)
  obtain ⟨C, hC, hestimate⟩ := raw_quadratic_heat_weighted_bound P G hT hTlt hc hd ha
    (show 0 ≤ (17 * B + 1) * I by positivity) F hFcont (fun s _ y => hF s y)
    hFinit hFs hFd
  refine ⟨C, hC, ?_⟩
  intro s hs y
  have hQF : Q s y ≤ F s y := by
    calc
      Q s y = 1 * Q s y := by rw [one_mul]
      _ ≤ (16 * B + 1 + q s y) * Q s y :=
        mul_le_mul_of_nonneg_right (by have := hq s y; nlinarith) (hQ s y)
  exact (mul_le_mul_of_nonneg_left hQF (add_nonneg ha hs.1)).trans (hestimate s hs y)

end PoincareConjecture.M35.Uniqueness
