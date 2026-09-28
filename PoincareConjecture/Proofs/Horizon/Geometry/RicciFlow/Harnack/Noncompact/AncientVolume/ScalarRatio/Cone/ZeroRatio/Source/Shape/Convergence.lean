import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

private theorem tendsto_clm_apply
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {A : ι → E →L[ℝ] F} {a : E →L[ℝ] F}
    {v : ι → E} {w : E} (hA : Tendsto A l (𝓝 a)) (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (a w)) :=
  (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hA.prodMk_nhds hv)

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem tendsto_gradient_of_metric_coefficients
    {ι : Type*} {l : Filter ι} {gseq : ι → RiemannianMetric n E}
    {g : RiemannianMetric n E} (Dseq : ∀ i, LeviCivitaData (gseq i))
    (D : LeviCivitaData g) {xseq : ι → E} {x : E} {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hx : Tendsto xseq l (𝓝 x))
    (hmetric : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x))) :
    Tendsto (fun i => (Dseq i).gradient f (xseq i)) l (𝓝 (D.gradient f x)) := by
  have hgi : (g.euclideanCoefficients x).IsInvertible := g.inner_isInvertible x
  have hi := hgi.contDiffAt_map_inverse
    (n := ∞) |>.continuousAt.tendsto.comp hmetric
  have hd := (hf.fderiv_right (m := ∞) (by simp)).continuous.continuousAt.tendsto.comp hx
  have h := tendsto_clm_apply hi hd
  have heq (g' : RiemannianMetric n E) (D' : LeviCivitaData g') (y : E) :
      D'.gradient f y = (g'.euclideanCoefficients y).inverse (fderiv ℝ f y) := by
    unfold gradient
    congr 1
    ext v
    simp +instances [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  simpa only [heq, Function.comp_apply] using h

theorem tendsto_levelQ_of_metric_coefficients
    {ι : Type*} {l : Filter ι} {gseq : ι → RiemannianMetric n E}
    {g : RiemannianMetric n E} (Dseq : ∀ i, LeviCivitaData (gseq i))
    (D : LeviCivitaData g) {xseq : ι → E} {x : E} {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hx : Tendsto xseq l (𝓝 x))
    (hmetric : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x))) :
    Tendsto (fun i => (Dseq i).levelQ f (xseq i)) l (𝓝 (D.levelQ f x)) := by
  have hgrad := tendsto_gradient_of_metric_coefficients Dseq D hf hx hmetric
  exact tendsto_clm_apply (tendsto_clm_apply hmetric hgrad) hgrad

theorem tendsto_hessian_of_metric_coefficients
    {ι : Type*} {l : Filter ι} {gseq : ι → RiemannianMetric n E}
    {g : RiemannianMetric n E} (Dseq : ∀ i, LeviCivitaData (gseq i))
    (D : LeviCivitaData g) {xseq vseq wseq : ι → E} {x v w : E} {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hx : Tendsto xseq l (𝓝 x))
    (hv : Tendsto vseq l (𝓝 v)) (hw : Tendsto wseq l (𝓝 w))
    (hmetric : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)))
    (hfirst : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x))) :
    Tendsto (fun i => (Dseq i).hessian f (xseq i) (vseq i) (wseq i)) l
      (𝓝 (D.hessian f x v w)) := by
  have hgi : (g.euclideanCoefficients x).IsInvertible := g.inner_isInvertible x
  have hi := hgi.contDiffAt_map_inverse
    (n := ∞) |>.continuousAt.tendsto.comp hmetric
  have hk : Continuous (fun z : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) × E × E =>
      metricKoszulCovector z.1 z.2.1 z.2.2) := by
    have hflip : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
    have hflip' : Continuous (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous
    unfold metricKoszulCovector
    fun_prop
  have hkoszul := hk.continuousAt.tendsto.comp
    (hfirst.prodMk_nhds (hv.prodMk_nhds hw))
  have hchrist := tendsto_clm_apply hi hkoszul
  change Tendsto (fun i => CoordinateExponential.christoffelBilinear
    (gseq i).euclideanCoefficients (xseq i) (vseq i) (wseq i)) l
      (𝓝 (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x v w)) at hchrist
  have hd := (hf.fderiv_right (m := ∞) (by simp)).continuous.continuousAt.tendsto.comp hx
  have hdd := ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
    |>.continuousAt.tendsto.comp hx
  have h := (tendsto_clm_apply (tendsto_clm_apply hdd hv) hw).sub
    (tendsto_clm_apply hd hchrist)
  simpa only [hessian_eq_fderiv_sub_christoffel _ hf.contDiffAt, Function.comp_apply] using h

theorem tendsto_levelShapeRatio_of_metric_coefficients
    {ι : Type*} {l : Filter ι} {gseq : ι → RiemannianMetric n E}
    {g : RiemannianMetric n E} (Dseq : ∀ i, LeviCivitaData (gseq i))
    (D : LeviCivitaData g) {xseq vseq : ι → E} {x v : E} {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hx : Tendsto xseq l (𝓝 x))
    (hv : Tendsto vseq l (𝓝 v)) (hv0 : v ≠ 0)
    (hmetric : Tendsto (fun i => (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (g.euclideanCoefficients x)))
    (hfirst : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients (xseq i)) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (hH : D.hessian f x v v = g.inner x v v) (hQ : D.levelQ f x = 1) :
    Tendsto (fun i => (Dseq i).hessian f (xseq i) (vseq i) (vseq i) /
      (Real.sqrt ((Dseq i).levelQ f (xseq i)) *
        (gseq i).inner (xseq i) (vseq i) (vseq i))) l (𝓝 1) := by
  have hHess := tendsto_hessian_of_metric_coefficients Dseq D hf hx hv hv hmetric hfirst
  have hnorm := tendsto_clm_apply (tendsto_clm_apply hmetric hv) hv
  change Tendsto (fun i => (gseq i).inner (xseq i) (vseq i) (vseq i)) l
    (𝓝 (g.inner x v v)) at hnorm
  have hgrad := tendsto_levelQ_of_metric_coefficients Dseq D hf hx hmetric
  have hpos := g.pos x v hv0
  have hratio := hHess.div ((Real.continuous_sqrt.tendsto _ |>.comp hgrad).mul hnorm)
    (by simpa only [hQ, Real.sqrt_one, one_mul] using ne_of_gt hpos)
  rw [hH, hQ, Real.sqrt_one, one_mul, div_self (ne_of_gt hpos)] at hratio
  exact hratio

private theorem eventually_forall_compact_of_moving_points
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {P : ℕ → X → Prop}
    (hstable : ∀ (indices : ℕ → ℕ), Tendsto indices atTop atTop →
      ∀ (points : ℕ → X), (∀ k, points k ∈ K) →
      ∀ x ∈ K, Tendsto points atTop (𝓝 x) → ∀ᶠ k in atTop, P (indices k) (points k)) :
    ∀ᶠ k in atTop, ∀ x ∈ K, P k x := by
  classical
  by_contra h
  have hbad : ∀ k : ℕ, ∃ j, k ≤ j ∧ ∃ x ∈ K, ¬ P j x := by
    rw [eventually_atTop] at h
    push Not at h
    exact h
  choose indices hindices points hpoints hbad using hbad
  obtain ⟨x, hx, σ, hσ, hlim⟩ := hK.tendsto_subseq hpoints
  have hind : Tendsto (fun k => indices (σ k)) atTop atTop :=
    (tendsto_atTop_mono hindices tendsto_id).comp hσ.tendsto_atTop
  obtain ⟨k, hk⟩ := (hstable _ hind (points ∘ σ) (fun k => hpoints (σ k)) x hx hlim).exists
  exact hbad (σ k) hk

theorem eventually_levelQ_pos_of_uniform_metric_coefficients
    {gseq : ℕ → RiemannianMetric n E} {g : RiemannianMetric n E}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hmetric : TendstoUniformlyOn (fun k => (gseq k).euclideanCoefficients)
      g.euclideanCoefficients atTop K)
    (hQ : ∀ x ∈ K, D.levelQ f x = 1) :
    ∀ᶠ k in atTop, ∀ x ∈ K, 0 < (Dseq k).levelQ f x := by
  apply eventually_forall_compact_of_moving_points hK
  intro indices hi points hp x hx hlim
  have hwithin : Tendsto points atTop (𝓝[K] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, .of_forall hp⟩
  have hm := (hmetric.seq_tendstoUniformlyOn indices hi).tendsto_comp
    (g.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt hwithin
  have h := tendsto_levelQ_of_metric_coefficients (fun k => Dseq (indices k)) D hf hlim hm
  rw [hQ x hx] at h
  exact tendsto_const_nhds.eventually_lt h zero_lt_one

theorem eventually_levelShapeRatio_on_unit_vectors
    {gseq : ℕ → RiemannianMetric n E} {g : RiemannianMetric n E}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hmetric : TendstoUniformlyOn (fun k => (gseq k).euclideanCoefficients)
      g.euclideanCoefficients atTop K)
    (hfirst : TendstoUniformlyOn (fun k => fderiv ℝ (gseq k).euclideanCoefficients)
      (fderiv ℝ g.euclideanCoefficients) atTop K)
    (hH : ∀ x ∈ K, ∀ v, D.hessian f x v v = g.inner x v v)
    (hQ : ∀ x ∈ K, D.levelQ f x = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : E, ‖v‖ = 1 →
      (Dseq k).hessian f x v v /
          (Real.sqrt ((Dseq k).levelQ f x) * (gseq k).inner x v v) ∈ Ioo (1 - ε) (1 + ε) := by
  have hcompact := hK.prod (isCompact_sphere (0 : E) 1)
  have hgood : ∀ᶠ k in atTop, ∀ z ∈ K ×ˢ Metric.sphere (0 : E) 1,
      (Dseq k).hessian f z.1 z.2 z.2 /
          (Real.sqrt ((Dseq k).levelQ f z.1) * (gseq k).inner z.1 z.2 z.2) ∈
        Ioo (1 - ε) (1 + ε) := by
    apply eventually_forall_compact_of_moving_points hcompact
    intro indices hi points hp z hz hlim
    have hx : Tendsto (fun k => (points k).1) atTop (𝓝 z.1) :=
      continuous_fst.continuousAt.tendsto.comp hlim
    have hv : Tendsto (fun k => (points k).2) atTop (𝓝 z.2) :=
      continuous_snd.continuousAt.tendsto.comp hlim
    have hwithin : Tendsto (fun k => (points k).1) atTop (𝓝[K] z.1) :=
      tendsto_nhdsWithin_iff.mpr ⟨hx, .of_forall fun k => (hp k).1⟩
    have hm := (hmetric.seq_tendstoUniformlyOn indices hi).tendsto_comp
      (g.contDiffAt_euclideanCoefficients z.1).continuousAt.continuousWithinAt hwithin
    have hcont := ((g.contDiffAt_euclideanCoefficients z.1).fderiv_right
      (m := ∞) (by simp)).continuousAt.continuousWithinAt (s := K)
    have hd := (hfirst.seq_tendstoUniformlyOn indices hi).tendsto_comp hcont hwithin
    have hv0 : z.2 ≠ 0 := by
      have hn : ‖z.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
      intro hzero
      simp [hzero] at hn
    have h := tendsto_levelShapeRatio_of_metric_coefficients (fun k => Dseq (indices k)) D
      hf hx hv hv0 hm hd (hH z.1 hz.1 z.2) (hQ z.1 hz.1)
    exact h.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  filter_upwards [hgood] with k hk x hx v hv
  exact hk (x, v) ⟨hx, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩

private theorem hessian_smul_same {g : RiemannianMetric n E} (D : LeviCivitaData g)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v : E) (c : ℝ) :
    D.hessian f x (c • v) (c • v) = c ^ 2 * D.hessian f x v v := by
  rw [D.hessian_eq_fderiv_sub_christoffel hf.contDiffAt,
    D.hessian_eq_fderiv_sub_christoffel hf.contDiffAt]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem eventually_levelShape_quadratic_bounds
    {gseq : ℕ → RiemannianMetric n E} {g : RiemannianMetric n E}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K)
    (hmetric : TendstoUniformlyOn (fun k => (gseq k).euclideanCoefficients)
      g.euclideanCoefficients atTop K)
    (hfirst : TendstoUniformlyOn (fun k => fderiv ℝ (gseq k).euclideanCoefficients)
      (fderiv ℝ g.euclideanCoefficients) atTop K)
    (hH : ∀ x ∈ K, ∀ v, D.hessian f x v v = g.inner x v v)
    (hQ : ∀ x ∈ K, D.levelQ f x = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      0 < (Dseq k).levelQ f x ∧ ∀ v : E, v ≠ 0 →
        (1 - ε) * (gseq k).inner x v v <
            (Dseq k).hessian f x v v / Real.sqrt ((Dseq k).levelQ f x) ∧
        (Dseq k).hessian f x v v / Real.sqrt ((Dseq k).levelQ f x) <
            (1 + ε) * (gseq k).inner x v v := by
  filter_upwards [eventually_levelQ_pos_of_uniform_metric_coefficients Dseq D hf hK hmetric hQ,
    eventually_levelShapeRatio_on_unit_vectors Dseq D hf hK hmetric hfirst hH hQ hε]
    with k hreg hratio x hx
  refine ⟨hreg x hx, ?_⟩
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, ne_of_gt hn]
  have hunit := hratio x hx (‖v‖⁻¹ • v) hu
  have heq : (Dseq k).hessian f x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) /
      (Real.sqrt ((Dseq k).levelQ f x) *
        (gseq k).inner x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v)) =
      (Dseq k).hessian f x v v /
        (Real.sqrt ((Dseq k).levelQ f x) * (gseq k).inner x v v) := by
    rw [hessian_smul_same _ hf]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hfactor : Real.sqrt ((Dseq k).levelQ f x) *
        (‖v‖⁻¹ * (‖v‖⁻¹ * (gseq k).inner x v v)) =
        (‖v‖⁻¹) ^ 2 * (Real.sqrt ((Dseq k).levelQ f x) * (gseq k).inner x v v) := by ring
    rw [hfactor, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero (ne_of_gt hn)))]
  rw [heq, ← div_div] at hunit
  exact ⟨(lt_div_iff₀ ((gseq k).pos x v hv)).mp hunit.1,
    (div_lt_iff₀ ((gseq k).pos x v hv)).mp hunit.2⟩

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Hypersurface

open PoincareConjecture

variable {m : ℕ}
local notation "A" => EuclideanSpace ℝ (Fin (m + 1))
local notation "H" => EuclideanSpace ℝ (Fin m)

theorem inner_shapeOperator_neg_levelUnitNormal_of_level
    {g : RiemannianMetric (m + 1) A} {h : RiemannianMetric m H}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : A → ℝ} (hf : ContDiff ℝ ∞ f) {F : H → A} {V : Set H}
    (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F V) {c : ℝ}
    (hlevel : ∀ y ∈ V, f (F y) = c) {y : H} (hy : y ∈ V)
    (hreg : 0 < D.levelQ f (F y)) (u v : H) :
    h.inner y (shapeOperator D D' F y (-D.levelUnitNormal f (F y)) u) v =
      D.hessian f (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
        Real.sqrt (D.levelQ f (F y)) := by
  have hnormal (z : H) (hz : z ∈ V) (w : H) :
      g.inner (F z) (D.levelUnitNormal f (F z)) (fderiv ℝ F z w) = 0 := by
    have hconst : (f ∘ F) =ᶠ[𝓝 z] fun _ => c := by
      filter_upwards [hV.mem_nhds hz] with z hz
      exact hlevel z hz
    have hchain := congrArg (fun L : H →L[ℝ] ℝ => L w)
      (fderiv_comp z (hf.differentiable (by simp) (F z))
        ((hF.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)))
    rw [hconst.fderiv_eq, fderiv_const_apply] at hchain
    have hzero : fderiv ℝ f (F z) (fderiv ℝ F z w) = 0 := by
      simpa only [zero_apply, ContinuousLinearMap.comp_apply] using hchain.symm
    rw [LeviCivitaData.levelUnitNormal]
    simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
    have hdf : mvfderiv (𝓡 (m + 1)) f (F z) (fderiv ℝ F z w) = 0 := by
      simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      exact hzero
    rw [hdf, mul_zero]
  have hnormal' : ∀ᶠ z in 𝓝 y, ∀ w,
      g.inner (F z) (D.levelUnitNormal f (F z)) (fderiv ℝ F z w) = 0 := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact hnormal z hz
  have hshape := inner_shapeOperator_eq_neg_levelHessian D D'
    (hF.contDiffAt (hV.mem_nhds hy))
    (contMDiffAt_iff_contDiffAt.mpr hf.contDiffAt) hreg
    (D.levelUnitNormal f (F y)) rfl (hnormal y hy) hnormal' u v
  have hneg : h.inner y (shapeOperator D D' F y (-D.levelUnitNormal f (F y)) u) v =
      -h.inner y (shapeOperator D D' F y (D.levelUnitNormal f (F y)) u) v := by
    rw [inner_shapeOperator, inner_shapeOperator]
    simp only [map_neg, neg_apply]
  rw [hneg, hshape, neg_div, neg_neg]

theorem shapeOperator_eigenvalue_mem_Ioo_of_levelShape_bounds
    {g : RiemannianMetric (m + 1) A} {h : RiemannianMetric m H}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : A → ℝ} (hf : ContDiff ℝ ∞ f) {F : H → A} {V : Set H}
    (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F V) {c : ℝ}
    (hlevel : ∀ y ∈ V, f (F y) = c) {y : H} (hy : y ∈ V)
    (hmetric : ∀ u v, h.inner y u v = g.inner (F y) (fderiv ℝ F y u) (fderiv ℝ F y v))
    (hreg : 0 < D.levelQ f (F y)) {ε : ℝ}
    (hshape : ∀ v : A, v ≠ 0 →
      (1 - ε) * g.inner (F y) v v < D.hessian f (F y) v v / Real.sqrt (D.levelQ f (F y)) ∧
      D.hessian f (F y) v v / Real.sqrt (D.levelQ f (F y)) < (1 + ε) * g.inner (F y) v v)
    {κ : ℝ} (hκ : Module.End.HasEigenvalue
      (shapeOperator D D' F y (-D.levelUnitNormal f (F y))) κ) :
    κ ∈ Ioo (1 - ε) (1 + ε) := by
  obtain ⟨v, hv⟩ := hκ.exists_hasEigenvector
  have hvpos := h.pos y v hv.2
  have hdv : fderiv ℝ F y v ≠ 0 := by
    intro hzero
    have hzero' := hmetric v v
    simp only [hzero, map_zero] at hzero'
    linarith
  have hpinch := hshape (fderiv ℝ F y v) hdv
  rw [← hmetric v v] at hpinch
  have hpair := inner_shapeOperator_neg_levelUnitNormal_of_level D D' hf hV hF
    hlevel hy hreg v v
  rw [hv.apply_eq_smul] at hpair
  simp only [map_smul, smul_apply, smul_eq_mul] at hpair
  rw [← hpair] at hpinch
  exact ⟨(mul_lt_mul_iff_left₀ hvpos).mp hpinch.1,
    (mul_lt_mul_iff_left₀ hvpos).mp hpinch.2⟩

theorem eventually_principalCurvatures_near_one
    {gseq : ℕ → RiemannianMetric (m + 1) A} {g : RiemannianMetric (m + 1) A}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    {f : A → ℝ} (hf : ContDiff ℝ ∞ f) {K : Set A} (hK : IsCompact K)
    (hmetric : TendstoUniformlyOn (fun k => (gseq k).euclideanCoefficients)
      g.euclideanCoefficients atTop K)
    (hfirst : TendstoUniformlyOn (fun k => fderiv ℝ (gseq k).euclideanCoefficients)
      (fderiv ℝ g.euclideanCoefficients) atTop K)
    (hH : ∀ x ∈ K, ∀ v, D.hessian f x v v = g.inner x v v)
    (hQ : ∀ x ∈ K, D.levelQ f x = 1)
    {hseq : ℕ → RiemannianMetric m H} (D'seq : ∀ k, LeviCivitaData (hseq k))
    {F : H → A} {V : Set H} (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F V)
    {c : ℝ} (hlevel : ∀ y ∈ V, f (F y) = c)
    (hinduced : ∀ k y, y ∈ V → ∀ u v,
      (hseq k).inner y u v = (gseq k).inner (F y) (fderiv ℝ F y u) (fderiv ℝ F y v))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ y ∈ V, F y ∈ K →
      0 < (Dseq k).levelQ f (F y) ∧ ∀ κ : ℝ,
        Module.End.HasEigenvalue
          (shapeOperator (Dseq k) (D'seq k) F y (-(Dseq k).levelUnitNormal f (F y))) κ →
        κ ∈ Ioo (1 - ε) (1 + ε) := by
  filter_upwards [LeviCivitaData.eventually_levelShape_quadratic_bounds Dseq D
    hf hK hmetric hfirst hH hQ hε] with k hk y hy hyK
  refine ⟨(hk (F y) hyK).1, ?_⟩
  intro κ hκ
  exact shapeOperator_eigenvalue_mem_Ioo_of_levelShape_bounds (Dseq k) (D'seq k)
    hf hV hF hlevel hy (hinduced k y hy) (hk (F y) hyK).1 (hk (F y) hyK).2 hκ

end Poincare.Geometry.Curvature.Hypersurface
