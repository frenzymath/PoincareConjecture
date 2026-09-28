import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ChartSegment
import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.Derivative








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]




theorem eventually_metric_chart_distortion (p : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 p, ‖((trivializationAt E (TangentSpace I) p).symmL ℝ p) ∘L
      ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ y)‖ < r := by
  exact eventually_norm_symmL_trivializationAt_self_comp_lt E
    (TangentSpace I) p hr



theorem eventually_metric_chart_distortion_reverse (p : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 p, ‖((trivializationAt E (TangentSpace I) p).symmL ℝ y) ∘L
      ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p)‖ < r := by
  exact eventually_norm_symmL_trivializationAt_comp_self_lt E
    (TangentSpace I) p hr



theorem eventually_metric_extChart_deriv_bound (p : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 p, ‖((trivializationAt E (TangentSpace I) p).symmL ℝ p) ∘L
      (mfderiv% (extChartAt I p) y)‖ < r := by
  filter_upwards [eventually_metric_chart_distortion (E := E) (I := I) p hr,
    chart_source_mem_nhds (H := H) p] with y hdist hsource
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (E := E) hsource]
  exact hdist

theorem eventually_metric_extChart_inverse_deriv_bound (p : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 p, ‖(mfderiv[range ↑I] (extChartAt I p).symm
      (extChartAt I p y)) ∘L
      ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p)‖ < r := by
  filter_upwards [eventually_metric_chart_distortion_reverse (E := E) (I := I) p hr,
    chart_source_mem_nhds (H := H) p] with y hdist hsource
  rw [TangentBundle.symmL_trivializationAt (I := I) (E := E) hsource] at hdist
  convert! hdist using 3 <;> congr
  all_goals exact (extChartAt I p).left_inv (by simpa [extChartAt_source] using hsource)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]

set_option backward.isDefEq.respectTransparency false in


theorem exists_local_distance_approx (g : RiemannianMetric n M) (O p : M) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ ∀ ε : ℝ, 0 < ε → ∃ f : M → ℝ,
      (∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f x) ∧
      (∀ x ∈ U, |f x - (g.edist O x).toReal| ≤ ε) ∧
      (∀ x ∈ U, ∀ v,
        |mvfderiv (𝓡 n) f x v| ≤ (3 / 2 : ℝ) * g.tangentNorm x v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let e := extChartAt (𝓡 n) p
  let A : TangentSpace (𝓡 n) p ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearEquivAt
      ℝ p (FiberBundle.mem_baseSet_trivializationAt' p)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    FiniteDimensional.of_injective A.toLinearMap A.injective
  let ψ : M → TangentSpace (𝓡 n) p := A.symm ∘ e
  let Φ : TangentSpace (𝓡 n) p → M := e.symm ∘ A
  have hψ (y : M) (hy : y ∈ e.source) :
      ContMDiffAt (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p)) ∞ ψ y := by
    exact A.symm.contDiff.contMDiff.contMDiffAt.comp y
      (contMDiffAt_extChartAt' (by simpa [e] using hy))
  have hΦ (z : TangentSpace (𝓡 n) p) (hz : A z ∈ e.target) :
      ContMDiffAt (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n) ∞ Φ z := by
    have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm (A z) := by
      simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using
        contMDiffWithinAt_extChartAt_symm_range (n := ∞) p hz
    exact hi.comp z A.contDiff.contMDiff.contMDiffAt
  have hleft (y : M) (hy : y ∈ e.source) : Φ (ψ y) = y := by
    simp only [Φ, ψ, Function.comp_apply, A.apply_symm_apply, e.left_inv hy]
  have hright (z : TangentSpace (𝓡 n) p) (hz : A z ∈ e.target) : ψ (Φ z) = z := by
    simp only [Φ, ψ, Function.comp_apply, e.right_inv hz, A.symm_apply_apply]
  have hforward : ∀ᶠ y in 𝓝 p,
      ‖A.symm.toContinuousLinearMap ∘L
        mfderiv (𝓡 n) (𝓡 n) e y‖ < (6 / 5 : ℝ) := by
    simpa only [A, Bundle.Trivialization.symm_continuousLinearEquivAt_eq'] using
      eventually_metric_extChart_deriv_bound (I := 𝓡 n) p (by norm_num : (1 : ℝ) < 6 / 5)
  have hreverse : ∀ᶠ y in 𝓝 p,
      ‖mfderiv (𝓡 n) (𝓡 n) e.symm (e y) ∘L
        A.toContinuousLinearMap‖ < (6 / 5 : ℝ) := by
    simpa only [A, Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
      modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] using
      eventually_metric_extChart_inverse_deriv_bound (I := 𝓡 n) p
        (by norm_num : (1 : ℝ) < 6 / 5)
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz₀ : A (ψ p) ∈ e.target := by
    simpa only [ψ, Function.comp_apply, A.apply_symm_apply] using e.map_source hp
  have htarget : e.target ∈ 𝓝 (e p) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓡 n) p
  have htA : ∀ᶠ z in 𝓝 (ψ p), A z ∈ e.target := by
    apply A.continuous.continuousAt.eventually
    change e.target ∈ 𝓝 (A (ψ p))
    simpa only [ψ, Function.comp_apply, A.apply_symm_apply] using htarget
  have hb := (hΦ _ hz₀).continuousAt.eventually
    (show ∀ᶠ y in 𝓝 (Φ (ψ p)),
      ‖A.symm.toContinuousLinearMap ∘L mfderiv (𝓡 n) (𝓡 n) e y‖ < (6 / 5 : ℝ) ∧
      ‖mfderiv (𝓡 n) (𝓡 n) e.symm (e y) ∘L A.toContinuousLinearMap‖ < (6 / 5 : ℝ)
      from (hleft p hp).symm ▸ hforward.and hreverse)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (htA.and hb)
  have hdΦ (z : TangentSpace (𝓡 n) p) (hz : A z ∈ e.target) :
      mfderiv (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n) Φ z =
        mfderiv (𝓡 n) (𝓡 n) e.symm (A z) ∘L A.toContinuousLinearMap := by
    have hi : MDifferentiableAt (𝓡 n) (𝓡 n) e.symm (A z) := by
      simpa only [modelWithCornersSelf_coe, Set.range_id, mdifferentiableWithinAt_univ] using
        mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 n) hz
    rw [show Φ = e.symm ∘ A from rfl, mfderiv_comp z hi A.differentiableAt.mdifferentiableAt,
      mfderiv_eq_fderiv, A.fderiv]
  have hboundΦ (z : TangentSpace (𝓡 n) p) (hz : z ∈ Metric.ball (ψ p) r) :
      ‖mfderiv (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n) Φ z‖ₑ ≤ (6 / 5 : ℝ≥0) := by
    have hh := (hball hz).2.2
    have he : e (Φ z) = A z := e.right_inv (hball hz).1
    rw [he] at hh
    rw [hdΦ z (hball hz).1]
    exact_mod_cast hh.le
  let R : TangentSpace (𝓡 n) p → ℝ := fun z ↦ (g.edist O (Φ z)).toReal
  have hR : LipschitzOnWith (6 / 5 : ℝ≥0) R (Metric.ball (ψ p) r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz w hw
    have hh := Poincare.riemannianEDist_le_mul_edist_of_convex
      (convex_ball _ _) (fun q hq ↦ (hΦ q (hball hq).1).of_le (by simp))
      hboundΦ hz hw
    have hfinite : ((6 / 5 : ℝ≥0) : ℝ≥0∞) * EDist.edist z w ≠ ⊤ := by finiteness
    have hreal := ENNReal.toReal_mono hfinite hh
    have hd : (g.edist (Φ z) (Φ w)).toReal ≤ (6 / 5 : ℝ) * dist z w := by
      simpa only [edist, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_div,
        NNReal.coe_ofNat, edist_dist, ENNReal.toReal_ofReal (dist_nonneg)] using hreal
    exact (g.abs_toReal_edist_sub_le O (Φ z) (Φ w)).trans hd
  obtain ⟨Rext, hRext, hReq⟩ := hR.extend_real
  let U := e.source ∩ ψ ⁻¹' Metric.ball (ψ p) r
  refine ⟨U, ?_, ?_⟩
  · exact inter_mem (by simpa only [e, extChartAt_source] using
        chart_source_mem_nhds (EuclideanSpace ℝ (Fin n)) p)
      ((hψ p hp).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  intro ε hε
  obtain ⟨u, hu, huLip, huerr, hud⟩ := Poincare.exists_contDiff_lipschitz_approx hRext hε
  refine ⟨u ∘ ψ, ?_, ?_, ?_⟩
  · intro x hx
    exact hu.comp_contMDiffAt (hψ x hx.1)
  · intro x hx
    have hh := huerr (ψ x)
    rw [← hReq hx.2] at hh
    simpa only [R, hleft x hx.1, Function.comp_apply, Real.dist_eq] using hh
  · intro x hx v
    let := normedAddCommGroupTangentSpaceVectorSpace (e x)
    let := normedSpaceTangentSpaceVectorSpace (e x)
    let := normedAddCommGroupTangentSpaceVectorSpace (ψ x)
    let := normedSpaceTangentSpaceVectorSpace (ψ x)
    have hdx : MDifferentiableAt (𝓡 n) (𝓡 n) e x :=
      (contMDiffAt_extChartAt' (n := ∞)
        (by simpa only [e, extChartAt_source] using hx.1)).mdifferentiableAt (by simp)
    have hdψ : mfderiv (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p)) ψ x =
        A.symm.toContinuousLinearMap ∘L mfderiv (𝓡 n) (𝓡 n) e x := by
      rw [show ψ = A.symm ∘ e from rfl,
        mfderiv_comp x A.symm.differentiableAt.mdifferentiableAt hdx,
        mfderiv_eq_fderiv, A.symm.fderiv]
    have hψbound := (hball hx.2).2.1
    rw [hleft x hx.1] at hψbound
    rw [mvfderiv_comp x (hu.differentiable (by simp) (ψ x)).mdifferentiableAt
      ((hψ x hx.1).mdifferentiableAt (by simp))]
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    change |fderiv ℝ u (ψ x) (mfderiv (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p)) ψ x v)| ≤ _
    rw [hdψ, ← Real.norm_eq_abs]
    have hv := (A.symm.toContinuousLinearMap ∘L mfderiv (𝓡 n) (𝓡 n) e x).le_opNorm v
    have hn : ‖v‖ = g.tangentNorm x v := rfl
    rw [hn] at hv
    have hvbound := hv.trans (mul_le_mul_of_nonneg_right hψbound.le (Real.sqrt_nonneg _))
    have huapp := (fderiv ℝ u (ψ x)).le_opNorm
      ((A.symm.toContinuousLinearMap ∘L mfderiv (𝓡 n) (𝓡 n) e x) v)
    apply huapp.trans
    have hmult := mul_le_mul (hud (ψ x)) hvbound (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ (6 / 5 : ℝ≥0))
    have hN : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat] at hmult
    nlinarith

end PoincareConjecture.RiemannianMetric
