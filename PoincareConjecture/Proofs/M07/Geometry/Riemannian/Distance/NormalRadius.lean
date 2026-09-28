import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem inner_self_nonneg (g : RiemannianMetric n M) (p : M)
    (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.inner p v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos p v hv).le

theorem hasFDerivAt_regularized_tangentNorm
    (g : RiemannianMetric n M) (p : M) {ε : ℝ} (hε : 0 < ε)
    (v : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt (g.inner p w w + ε))
      ((Real.sqrt (g.inner p v v + ε))⁻¹ • g.inner p v) v := by
  have hpos : 0 < g.inner p v v + ε := add_pos_of_nonneg_of_pos
    (inner_self_nonneg g p v) hε
  have hquad := (g.inner p : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.clm_apply (hasFDerivAt_id v)
  have h := (hquad.add_const ε).sqrt hpos.ne'
  convert! h using 1
  ext w
  change (Real.sqrt (g.inner p v v + ε))⁻¹ * g.inner p v w =
    1 / (2 * Real.sqrt (g.inner p v v + ε)) * (g.inner p v w + g.inner p w v)
  rw [g.symm p w v]
  ring

theorem contDiff_regularized_tangentNorm
    (g : RiemannianMetric n M) (p : M) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt (g.inner p w w + ε)) := by
  apply ContDiff.sqrt
  · let B : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := g.inner p
    change ContDiff ℝ ∞ (fun w => B w w + ε)
    fun_prop
  · intro w
    exact (add_pos_of_nonneg_of_pos (inner_self_nonneg g p w) hε).ne'

theorem regularized_tangentNorm_mfderiv_le
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (hgauss : ∀ v ∈ e.source, ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w)
    {ε : ℝ} (hε : 0 < ε) {q : M} (hq : q ∈ e.target)
    (u : TangentSpace (𝓡 n) q) :
    |mvfderiv (𝓡 n)
      (fun y => Real.sqrt (g.inner p (e.symm y) (e.symm y) + ε)) q u| ≤
      g.tangentNorm q u := by
  let E := EuclideanSpace ℝ (Fin n)
  let v : E := e.symm q
  let w : E := mfderiv (𝓡 n) (𝓡 n) e.symm q u
  let z : TangentSpace (𝓡 n) q := mfderiv (𝓡 n) (𝓡 n) e v v
  have hv : v ∈ e.source := e.map_target hq
  have hediff : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), he'.mdifferentiableOn (by simp)⟩
  have hback : mfderiv (𝓡 n) (𝓡 n) e v w = u := by
    exact congrArg (fun L => L u) (hediff.comp_symm_deriv hq)
  have hrad : g.inner q z z = g.inner p v v := by
    have hh := hgauss v hv v
    change g.inner (e (e.symm q)) z z = g.inner p v v at hh
    rwa [e.right_inv hq] at hh
  have hpair : g.inner q z u = g.inner p v w := by
    have hh := hgauss v hv w
    rw [hback] at hh
    change g.inner (e (e.symm q)) z u = g.inner p v w at hh
    rwa [e.right_inv hq] at hh
  have hcs : g.inner p v w ^ 2 ≤ g.inner p v v * g.inner q u u := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h : (g.inner q z u) ^ 2 ≤ g.inner q z z * g.inner q u u := by
      change (inner ℝ z u) ^ 2 ≤ inner ℝ z z * inner ℝ u u
      simpa [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le z u
    rwa [hrad, hpair] at h
  have hchain : mvfderiv (𝓡 n)
      (fun y => Real.sqrt (g.inner p (e.symm y) (e.symm y) + ε)) q u =
      g.inner p v w / Real.sqrt (g.inner p v v + ε) := by
    have hd := g.hasFDerivAt_regularized_tangentNorm p hε v
    have hc := mfderiv_comp q
      (mdifferentiableAt_iff_differentiableAt.mpr hd.differentiableAt)
      (hediff.mdifferentiableAt_symm hq)
    rw [mfderiv_eq_fderiv] at hc
    change _ = (fderiv ℝ (fun w : E => Real.sqrt (g.inner p w w + ε)) v).comp
      (mfderiv (𝓡 n) (𝓡 n) e.symm q) at hc
    rw [hd.fderiv] at hc
    have hc' := congrArg (fun L => L u) hc
    simpa only [mvfderiv, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm,
      v, w] using! hc'
  rw [hchain, abs_div, abs_of_pos (Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (inner_self_nonneg g p v) hε))]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (inner_self_nonneg g p v) hε))).mpr
  have hnonneg := inner_self_nonneg g q u
  have hpnonneg := inner_self_nonneg g p v
  have hs := Real.sq_sqrt (show 0 ≤ g.inner p v v + ε by positivity)
  have hu := Real.sq_sqrt hnonneg
  have hsnonneg := Real.sqrt_nonneg (g.inner p v v + ε)
  have hunonneg := Real.sqrt_nonneg (g.inner q u u)
  change |g.inner p v w| ≤ Real.sqrt (g.inner q u u) * Real.sqrt (g.inner p v v + ε)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hunonneg hsnonneg)).mp
  rw [sq_abs, mul_pow, hu, hs]
  nlinarith [mul_nonneg hε.le hnonneg]

theorem exists_ball_tangentNorm_inverse_le_edist [T2Space M]
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source) (he0 : e 0 = p)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (hgauss : ∀ v ∈ e.source, ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w) :
    ∃ r : ℝ≥0, 0 < r ∧ {q | g.edist p q < r} ⊆ e.target ∧
      ∀ q, g.edist p q < r →
        ENNReal.ofReal (g.tangentNorm p (e.symm q)) ≤ g.edist p q := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  have hp : p ∈ e.target := he0 ▸ e.map_source h0
  obtain ⟨c, hc, hcs⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 n)
    (e.open_target.mem_nhds hp)
  let r : ℝ≥0 := c / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have h3r : 3 * (r : ℝ≥0∞) = c := by
    exact_mod_cast (show (3 : ℝ≥0) * (c / 3) = c by
      rw [mul_div_cancel₀ _ (by norm_num)])
  have hball : ∀ q, g.edist p q < 3 * (r : ℝ≥0∞) → q ∈ e.target := by
    intro q hq
    apply hcs
    simpa only [h3r] using! hq
  have hsmall : ∀ q, g.edist p q < r → q ∈ e.target := by
    intro q hq
    apply hball q
    exact hq.trans_le (by nth_rw 1 [← one_mul (r : ℝ≥0∞)]; gcongr; norm_num)
  refine ⟨r, hr, fun q hq => hsmall q hq, ?_⟩
  intro q hq
  have hεbound (ε : ℝ) (hε : 0 < ε) :
      EDist.edist (Real.sqrt ε)
        (Real.sqrt (g.inner p (e.symm q) (e.symm q) + ε)) ≤ g.edist p q := by
    let f : M → ℝ := fun y => Real.sqrt (g.inner p (e.symm y) (e.symm y) + ε)
    have hf : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 1 f y := by
      intro y hy
      exact ((contMDiff_iff_contDiff.mpr
        (g.contDiff_regularized_tangentNorm p hε)).contMDiffAt.comp y
          (he'.contMDiffAt (e.open_target.mem_nhds hy))).of_le (by simp)
    have hbound : ∀ y ∈ e.target,
        ‖mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) f y‖ₑ ≤ (1 : ℝ≥0) := by
      intro y hy
      simp only [ENNReal.coe_one]
      rw [← ENNReal.ofReal_one, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro u
      have hn : ‖mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) f y u‖ = |mvfderiv (𝓡 n) f y u| := by
        change ‖mvfderiv (𝓡 n) f y u‖ = |mvfderiv (𝓡 n) f y u|
        exact Real.norm_eq_abs _
      rw [one_mul, hn]
      exact g.regularized_tangentNorm_mfderiv_le p e he he' hgauss hε hy u
    have hd := Poincare.edist_le_mul_riemannianEDist_of_mfderiv_le_on_ball
      (I := 𝓡 n) (p := p) (r := r) (K := 1) (by norm_num)
      (fun y hy => hf y (hball y hy)) (fun y hy => hbound y (hball y hy))
      (x := p) (y := q) (by rw [riemannianEDist_self]; exact_mod_cast hr) hq
    have hep : e.symm p = 0 := by rw [← he0]; exact e.left_inv h0
    simpa [f, hep] using! hd
  have ht : Tendsto (fun ε : ℝ => EDist.edist (Real.sqrt ε)
      (Real.sqrt (g.inner p (e.symm q) (e.symm q) + ε))) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (g.tangentNorm p (e.symm q)))) := by
    have hcont : Continuous (fun ε : ℝ => EDist.edist (Real.sqrt ε)
        (Real.sqrt (g.inner p (e.symm q) (e.symm q) + ε))) :=
      Real.continuous_sqrt.edist (Real.continuous_sqrt.comp (continuous_const.add continuous_id))
    simpa [edist_dist, Real.dist_eq, tangentNorm, abs_of_nonneg, Real.sqrt_nonneg] using
      hcont.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε using hεbound ε hε

end PoincareConjecture.RiemannianMetric
