import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.DimensionOneLift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.HarmonicEstimate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Distance

set_option autoImplicit false

open Set
open Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
  [NoncompactSpace M]

namespace RiemannianMetric

variable (g : RiemannianMetric n M) (D : LeviCivitaData g)

structure HeatSolution where
  toFun : M → ℝ → ℝ
  smooth : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
    (fun p : M × ℝ ↦ toFun p.1 p.2) (univ ×ˢ Ioi 0)
  heatEquation : ∀ (t : ℝ), 0 < t → ∀ x : M,
    HasDerivAt (fun s ↦ toFun x s)
      (D.laplacian (fun y ↦ toFun y t) x) t

namespace HeatSolution

variable {g : RiemannianMetric n M} {D : LeviCivitaData g}

lemma contMDiff_slice (F : HeatSolution g D) {t : ℝ} (ht : 0 < t) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x ↦ F.toFun x t) := by
  exact contMDiff_slice_of_pos F.smooth ht

lemma deriv_eq_laplacian (F : HeatSolution g D) {t : ℝ} (ht : 0 < t) (x : M) :
    deriv (fun s ↦ F.toFun x s) t = D.laplacian (fun y ↦ F.toFun y t) x := by
  exact (F.heatEquation t ht x).deriv

omit [NoncompactSpace M] in

lemma abs_sub_center_le (F : HeatSolution g D) {u : M → ℝ} {A R t : ℝ}
    (hA : 0 ≤ A) (ht : 0 < t)
    (hvalue : ∀ x, |F.toFun x t - u x| ≤ A)
    (hgrad : ∀ x (v : TangentSpace (𝓡 n) x),
      |mvfderiv (𝓡 n) (fun y ↦ F.toFun y t) x v| ≤ A * g.tangentNorm x v)
    (x y : M) (hdist : (g.edist y x).toReal ≤ R) :
    |F.toFun y t - u x| ≤ (A + 1) * R + A := by
  let B : ℝ≥0 := ⟨A + 1, by linarith⟩
  have hB : 0 < B := by change 0 < A + 1; linarith
  have hgrad' : ∀ z v,
      |mvfderiv (𝓡 n) (fun w ↦ F.toFun w t) z v| ≤ B * g.tangentNorm z v := by
    intro z v
    exact (hgrad z v).trans (mul_le_mul_of_nonneg_right
      (by change A ≤ A + 1; linarith) (Real.sqrt_nonneg _))
  have hinc := g.abs_sub_le_mul_toReal_edist_of_derivative_bound
    (contMDiff_slice_of_pos F.smooth ht |>.of_le (by norm_cast)) hB hgrad' y x
  calc
    |F.toFun y t - u x| ≤ |F.toFun y t - F.toFun x t| + |F.toFun x t - u x| :=
      abs_sub_le _ _ _
    _ ≤ (A + 1) * (g.edist y x).toReal + A := add_le_add hinc (hvalue x)
    _ ≤ (A + 1) * R + A := add_le_add
      (mul_le_mul_of_nonneg_left hdist (show 0 ≤ A + 1 by linarith)) le_rfl

omit [T3Space M] [PreconnectedSpace M] [NoncompactSpace M] in

lemma hasDerivAt_lift_sub_const (F : HeatSolution g D)
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {h : RiemannianMetric n N} (D' : LeviCivitaData h)
    {f : N → M} {x : N} {t : ℝ} (ht : 0 < t) (c : ℝ)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      h.inner y a b = g.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b)) :
    HasDerivAt (fun s ↦ F.toFun (f x) s - c)
      (D'.laplacian (fun y ↦ F.toFun (f y) t - c) x) t := by
  have hslice := contMDiff_slice_of_pos F.smooth ht
  have hshift : D.laplacian (fun y ↦ F.toFun y t - c) (f x) =
      D.laplacian (fun y ↦ F.toFun y t) (f x) := by
    simp only [LeviCivitaData.laplacian, sub_eq_add_neg]
    simp_rw [D.hessian_add_const (hslice.mdifferentiable (by simp))]
  have hpull := D'.laplacian_comp_of_metric_pullback D hf hinv hmetric
    ((hslice (f x)).sub (contMDiffAt_const (c := c)))
  change D'.laplacian (fun y ↦ F.toFun (f y) t - c) x = _ at hpull
  rw [hpull, hshift]
  exact (F.heatEquation t ht (f x)).sub_const c

omit [T3Space M] [PreconnectedSpace M] [NoncompactSpace M] in

lemma hasDerivAt_harmonic_lift_sub_const (F : HeatSolution g D)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D' : LeviCivitaData h)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    {t : ℝ} (ht : 0 < t) (c : ℝ)
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace (𝓡 n) y,
      h.inner y v w = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y v) (mfderiv (𝓡 n) (𝓡 n) e y w))
    (hharm : ∀ i : Fin n,
      D'.laplacian (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x = 0) :
    HasDerivAt (fun s ↦ F.toFun (e x) s - c)
      (∑ i, ∑ j, h.inverseCoefficients x i j *
        fderiv ℝ (fderiv ℝ (fun y ↦ F.toFun (e y) t - c)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) t := by
  have hslice : ContDiffAt ℝ ∞ (fun y ↦ F.toFun (e y) t - c) x :=
    contMDiffAt_iff_contDiffAt.mp
      (((contMDiff_slice_of_pos F.smooth ht) (e x)).comp x he |>.sub contMDiffAt_const)
  have hheat := F.hasDerivAt_lift_sub_const D' ht c he hinv hmetric
  rw [D'.laplacian_eq_sum_fderiv_of_harmonic hslice hharm] at hheat
  exact hheat

set_option backward.isDefEq.respectTransparency false in
omit [T3Space M] [PreconnectedSpace M] [NoncompactSpace M] in

lemma norm_fderiv_lift_sub_const_le (F : HeatSolution g D)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    {t A b : ℝ} (ht : 0 < t) (hA : 0 ≤ A) (hb : 0 ≤ b) (c : ℝ)
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (hgrad : ∀ v : TangentSpace (𝓡 n) (e x),
      |mvfderiv (𝓡 n) (fun y ↦ F.toFun y t) (e x) v| ≤ A * g.tangentNorm (e x) v)
    (hmetric : ∀ v : EuclideanSpace ℝ (Fin n),
      g.pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) :
    ‖fderiv ℝ (fun y ↦ F.toFun (e y) t - c) x‖ ≤ A * Real.sqrt b := by
  rw [fderiv_sub_const]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hA (Real.sqrt_nonneg _))
  intro v
  have hs := (contMDiff_slice_of_pos F.smooth ht) (e x)
  have hd := mvfderiv_comp_apply x (hs.mdifferentiableAt (by simp))
    (he.mdifferentiableAt (by simp)) v
  have hnorm : g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤
      Real.sqrt b * ‖v‖ := by
    have hmetric' : g.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤
        b * ‖v‖ ^ 2 := by
      exact hmetric v
    have h := Real.sqrt_le_sqrt hmetric'
    simpa only [pullbackCoefficients, tangentNorm, Real.sqrt_mul hb,
      Real.sqrt_sq (norm_nonneg v)] using h
  have h := (hgrad (mfderiv (𝓡 n) (𝓡 n) e x v)).trans
    (mul_le_mul_of_nonneg_left hnorm hA)
  have hd' : fderiv ℝ (fun y ↦ F.toFun (e y) t) x v =
      mvfderiv (𝓡 n) (fun y ↦ F.toFun y t) (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) := by
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply] at hd
    convert! hd using 1
  rw [hd', Real.norm_eq_abs]
  simpa only [mul_assoc] using h

end HeatSolution

theorem exists_centered_arclength_heat_lift_one
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric 1 M) (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (F : HeatSolution g D) (u : M → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hvalue : ∀ t, 0 < t → t ≤ 1 → ∀ x, |F.toFun x t - u x| ≤ A)
    (hgrad : ∀ t, 0 < t → t ≤ 1 → ∀ x (v : TangentSpace (𝓡 1) x),
      |mvfderiv (𝓡 1) (fun y ↦ F.toFun y t) x v| ≤ A * g.tangentNorm x v)
    (p : M) :
    ∃ e : EuclideanSpace ℝ (Fin 1) → M,
      e 0 = p ∧ ContMDiffOn (𝓡 1) (𝓡 1) ∞ e (Metric.ball 0 2) ∧
      (∀ x ∈ Metric.ball 0 2, ∀ v w : EuclideanSpace ℝ (Fin 1),
        g.pullbackCoefficients e x v w = inner ℝ v w) ∧
      ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 1) × ℝ ↦
        F.toFun (e z.1) z.2 - u p) (Metric.ball 0 2 ×ˢ Ioi 0) ∧
      ∀ x ∈ Metric.ball 0 2, ∀ t, 0 < t →
        HasDerivAt (fun s ↦ F.toFun (e x) s - u p)
          (fderiv ℝ (fderiv ℝ (fun y ↦ F.toFun (e y) t - u p)) x
            (EuclideanSpace.basisFun (Fin 1) ℝ 0)
            (EuclideanSpace.basisFun (Fin 1) ℝ 0)) t ∧
        (t ≤ 1 → |F.toFun (e x) t - u p| ≤ 3 * A + 2) := by
  obtain ⟨e, he, hep, hmetric, hdist⟩ :=
    g.exists_arclength_lift_of_metricComplete_one hcomplete p (by norm_num : (0 : ℝ) < 2)
  let gE := euclideanMetric 1
  let DE := gE.euclideanLeviCivitaData
  have hsmooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : EuclideanSpace ℝ (Fin 1) × ℝ ↦ F.toFun (e z.1) z.2 - u p)
      (Metric.ball 0 2 ×ˢ Ioi 0) := by
    apply ContMDiffOn.sub _ contMDiffOn_const
    have hmap : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : EuclideanSpace ℝ (Fin 1) × ℝ ↦ (e z.1, z.2))
        (Metric.ball 0 2 ×ˢ Ioi 0) :=
      (he.comp contMDiffOn_fst (fun z hz ↦ hz.1)).prodMk contMDiffOn_snd
    exact F.smooth.comp hmap (fun z hz ↦ ⟨mem_univ _, hz.2⟩)
  simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hsmooth
  refine ⟨e, hep, he, hmetric, contMDiffOn_iff_contDiffOn.mp hsmooth, ?_⟩
  intro x hx t ht
  have heAt := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 1) (𝓡 1) e y).IsInvertible := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact g.isInvertible_mfderiv_of_euclidean_pullback_one (hmetric y hy)
  have hpull : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace (𝓡 1) y,
      gE.inner y v w = g.inner (e y)
        (mfderiv (𝓡 1) (𝓡 1) e y v) (mfderiv (𝓡 1) (𝓡 1) e y w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy v w
    exact (hmetric y hy v w).symm
  have hslice : ContDiffAt ℝ ∞ (fun y ↦ F.toFun (e y) t - u p) x :=
    contMDiffAt_iff_contDiffAt.mp
      (((contMDiff_slice_of_pos F.smooth ht) (e x)).comp x heAt |>.sub contMDiffAt_const)
  constructor
  · have hheat := F.hasDerivAt_lift_sub_const DE ht (u p) heAt hinv hpull
    rw [DE.laplacian_euclideanMetric hslice, Fin.sum_univ_one] at hheat
    exact hheat
  · intro ht1
    have hd : (g.edist (e x) p).toReal ≤ 2 := by
      have heq : g.edist (e x) p = g.edist p (e x) := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        exact Manifold.riemannianEDist_comm
      rw [heq]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdist x hx)).trans
        (by simpa only [ENNReal.toReal_ofReal (norm_nonneg x)] using
          (show ‖x‖ ≤ 2 from (mem_ball_zero_iff.mp hx).le))
    have hb := F.abs_sub_center_le hA ht (hvalue t ht ht1) (hgrad t ht ht1) p (e x) hd
    nlinarith

end RiemannianMetric

namespace LeviCivitaData

variable {g : RiemannianMetric n M} (D : LeviCivitaData g)

theorem abs_hessian_le_of_local_isometric_lift
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    {h : RiemannianMetric n N} (D' : LeviCivitaData h)
    {f : M → N} {x : M} {φ : N → ℝ}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x,
      (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    (hφ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ (f x))
    {C : ℝ}
    (hbound : ∀ v w : TangentSpace (𝓡 n) x,
      |D.hessian (φ ∘ f) x v w| ≤
        C * g.tangentNorm x v * g.tangentNorm x w)
    (v w : TangentSpace (𝓡 n) (f x)) :
    |D'.hessian φ (f x) v w| ≤
      C * h.tangentNorm (f x) v * h.tangentNorm (f x) w := by
  exact D.abs_hessian_le_of_metric_pullback D' hf hinv hmetric hφ hbound v w

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 8 in

theorem exists_uniform_hessian_bound_on_harmonic_lift
    (hn : 1 ≤ n) {r a b G A : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b)
    (hG : 0 ≤ G) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g)
        (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (Dh : LeviCivitaData h)
        (e : EuclideanSpace ℝ (Fin n) → M),
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 (r * 2)) →
        (∀ x ∈ Metric.ball 0 (r * 2), (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible) →
        (∀ x ∈ Metric.ball 0 (r * 2), h.euclideanCoefficients x = g.pullbackCoefficients e x) →
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ h.inner x v v ∧ h.inner x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 (r * 2), ‖fderiv ℝ h.euclideanCoefficients x‖ ≤ G) →
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ i : Fin n,
          Dh.laplacian (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x = 0) →
        ∀ (F : RiemannianMetric.HeatSolution g D) (u : M → ℝ),
          (∀ t, 0 < t → t ≤ 1 → ∀ x, |F.toFun x t - u x| ≤ A) →
          (∀ t, 0 < t → t ≤ 1 → ∀ x (v : TangentSpace (𝓡 n) x),
            |mvfderiv (𝓡 n) (fun y ↦ F.toFun y t) x v| ≤ A * g.tangentNorm x v) →
          ∀ v w : TangentSpace (𝓡 n) (e 0),
            |D.hessian (fun y ↦ F.toFun y 1) (e 0) v w| ≤
              C * g.tangentNorm (e 0) v * g.tangentNorm (e 0) w := by
  obtain ⟨C, hC, hestimate⟩ :=
    exists_uniform_harmonic_heat_second_derivative_bound n hn hr ha hab hG
  let B := (A + 1) * (Real.sqrt b * (r * 2)) + A
  let Q := (C * B + A * Real.sqrt b * ((3 / (2 * a)) * G)) / a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q + 1, by linarith, ?_⟩
  intro M _ _ _ _ _ g D h Dh e he hinv hmetric hell hderiv hharm F u hvalue hgrad v w
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 (r * 2) :=
    Metric.mem_ball_self (by positivity)
  have hdist (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (r * 2)) :
      (g.edist (e x) (e 0)).toReal ≤ Real.sqrt b * (r * 2) := by
    have hd := g.toReal_edist_le_of_pullback_upper Metric.isOpen_ball (convex_ball _ _)
      he (ha.le.trans hab) (fun z hz v ↦ by
        rw [← hmetric z hz]
        exact (hell z hz v).2) hx hzero
    exact hd.trans (mul_le_mul_of_nonneg_left (le_of_lt hx) (Real.sqrt_nonneg _))
  have hpull (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (r * 2)) :
      ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace (𝓡 n) y,
        h.inner y v w = g.inner (e y)
          (mfderiv (𝓡 n) (𝓡 n) e y v) (mfderiv (𝓡 n) (𝓡 n) e y w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy v w
    exact congrArg (fun L ↦ L v w) (hmetric y hy)
  have hi (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (r * 2)) :
      ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact hinv y hy
  have hsmooth : ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ F.toFun (e z.1) z.2 - u (e 0))
      (Metric.ball 0 (r * 2) ×ˢ Ioo 0 2) := by
    have hs : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ F.toFun (e z.1) z.2 - u (e 0))
        (Metric.ball 0 (r * 2) ×ˢ Ioo 0 2) := by
      apply ContMDiffOn.sub _ contMDiffOn_const
      exact F.smooth.comp
        ((he.comp contMDiffOn_fst (fun z hz ↦ hz.1)).prodMk contMDiffOn_snd)
        (fun z hz ↦ ⟨mem_univ _, hz.2.1⟩)
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hs
    exact contMDiffOn_iff_contDiffOn.mp hs
  have hsecond := hestimate h Dh hell hderiv hharm B hB
    (fun z ↦ F.toFun (e z.1) z.2 - u (e 0)) hsmooth
    (fun x hx t ht ↦ F.hasDerivAt_lift_sub_const Dh ht.1 (u (e 0))
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)) (hi x hx) (hpull x hx))
    (fun x hx t ht ↦ F.abs_sub_center_le hA ht.1 (hvalue t ht.1 ht.2)
      (hgrad t ht.1 ht.2) (e 0) (e x) (hdist x hx))
  have heAt := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hzero)
  have hfirst := F.norm_fderiv_lift_sub_const_le (by norm_num : (0 : ℝ) < 1)
    hA (ha.le.trans hab) (u (e 0)) heAt (hgrad 1 (by norm_num) le_rfl (e 0))
    (fun v ↦ by
      rw [← hmetric 0 hzero]
      exact (hell 0 hzero v).2)
  have hbound := Dh.abs_hessian_le_of_elliptic_coordinate_lift D (u (e 0))
    heAt (hi 0 hzero) (hpull 0 hzero)
    ((contMDiff_slice_of_pos F.smooth (by norm_num : (0 : ℝ) < 1)) (e 0))
    ha (fun v ↦ (hell 0 hzero v).1) hfirst hsecond (hderiv 0 hzero) v w
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

theorem exists_uniform_time_one_hessian_bound_one
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
        [IsManifold (𝓡 1) ∞ M] [T3Space M] [PreconnectedSpace M]
        (g : RiemannianMetric 1 M) (D : LeviCivitaData g),
        MetricComplete g →
        ∀ (F : RiemannianMetric.HeatSolution g D) (u : M → ℝ),
          (∀ t, 0 < t → t ≤ 1 → ∀ x, |F.toFun x t - u x| ≤ A) →
          (∀ t, 0 < t → t ≤ 1 → ∀ x (v : TangentSpace (𝓡 1) x),
            |mvfderiv (𝓡 1) (fun y ↦ F.toFun y t) x v| ≤ A * g.tangentNorm x v) →
          ∀ x (v w : TangentSpace (𝓡 1) x),
            |D.hessian (fun y ↦ F.toFun y 1) x v w| ≤
              C * g.tangentNorm x v * g.tangentNorm x w := by
  obtain ⟨C, hC, hestimate⟩ :=
    Poincare.Parabolic.Interior.exists_uniform_interior_heat_hessian_bound
      1 (by decide) 1 1 0 (by norm_num) le_rfl le_rfl
  refine ⟨C * (3 * A + 2), mul_pos hC (by linarith), ?_⟩
  intro M _ _ _ _ _ g D hcomplete F u hvalue hgrad p v w
  obtain ⟨e, hep, he, hmetric, hsmooth, hheat⟩ :=
    g.exists_centered_arclength_heat_lift_one D hcomplete F u hA hvalue hgrad p
  let a : EuclideanSpace ℝ (Fin 1) →
      EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    fun _ ↦ ContinuousLinearMap.id ℝ _
  have hsecond := hestimate a contDiffOn_const
    (by intro x hx v w; rfl)
    (by intro x hx v; simp [a])
    (by intro x hx y hy; simp [a])
    (3 * A + 2) (by linarith)
    (fun z ↦ F.toFun (e z.1) z.2 - u p)
    (hsmooth.mono (by intro z hz; exact ⟨hz.1, hz.2.1⟩))
    (by
      intro x hx t ht
      simpa [a, Fin.sum_univ_one] using (hheat x hx t ht.1).1)
    (by intro x hx t ht; exact (hheat x hx t ht.1).2 ht.2)
  let gE := RiemannianMetric.euclideanMetric 1
  let DE := gE.euclideanLeviCivitaData
  have hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ Metric.ball 0 2 := by simp
  have heAt := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hzero)
  have hinv : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 1)),
      (mfderiv (𝓡 1) (𝓡 1) e y).IsInvertible := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with y hy
    exact g.isInvertible_mfderiv_of_euclidean_pullback_one (hmetric y hy)
  have hpull : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 1)),
      ∀ v w : TangentSpace (𝓡 1) y,
      gE.inner y v w = g.inner (e y)
        (mfderiv (𝓡 1) (𝓡 1) e y v) (mfderiv (𝓡 1) (𝓡 1) e y w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with y hy v w
    exact (hmetric y hy v w).symm
  have hslice := contMDiff_slice_of_pos F.smooth (by norm_num : (0 : ℝ) < 1)
  have hcoord : ContDiffAt ℝ ∞ (fun y ↦ F.toFun (e y) 1) 0 :=
    contMDiffAt_iff_contDiffAt.mp ((hslice (e 0)).comp 0 heAt)
  have hshift : fderiv ℝ (fun y ↦ F.toFun (e y) 1 - u p) =
      fderiv ℝ (fun y ↦ F.toFun (e y) 1) := by
    funext y
    exact fderiv_sub_const (u p)
  rw [hshift] at hsecond
  have hb : ∀ v w : TangentSpace (𝓡 1) (e 0),
      |D.hessian (fun y ↦ F.toFun y 1) (e 0) v w| ≤
        (C * (3 * A + 2)) * g.tangentNorm (e 0) v * g.tangentNorm (e 0) w := by
    apply DE.abs_hessian_le_of_metric_pullback D heAt hinv hpull (hslice (e 0))
    intro v w
    change |DE.hessian (fun y ↦ F.toFun (e y) 1) 0 v w| ≤
      (C * (3 * A + 2)) * gE.tangentNorm 0 v * gE.tangentNorm 0 w
    rw [DE.hessian_euclideanMetric hcoord v w]
    rw [RiemannianMetric.euclideanMetric_tangentNorm (0 : EuclideanSpace ℝ (Fin 1)) v,
      RiemannianMetric.euclideanMetric_tangentNorm (0 : EuclideanSpace ℝ (Fin 1)) w]
    exact hsecond v w
  subst p
  exact hb v w

set_option backward.isDefEq.respectTransparency false in

theorem exists_uniform_time_one_hessian_bound
    {K A : ℝ} (hK : 0 < K) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
        [NoncompactSpace M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        ∀ (F : RiemannianMetric.HeatSolution g D) (u : M → ℝ),
          ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u →
          (∀ x (v w : TangentSpace (𝓡 n) x),
            |D.sectionalCurvature x v w| ≤ K) →
          (∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x : M,
            |F.toFun x t - u x| ≤ A) →
          (∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x (v : TangentSpace (𝓡 n) x),
            |mvfderiv (𝓡 n) (fun y ↦ F.toFun y t) x v| ≤
              A * g.tangentNorm x v) →
          ∀ x (v w : TangentSpace (𝓡 n) x),
            |D.hessian (fun y ↦ F.toFun y 1) x v w| ≤
              C * g.tangentNorm x v * g.tangentNorm x w := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro M _ _ _ _ _ _ g D
    have hdim := dimension_pos_of_noncompact (M := M) (n := 0)
    omega
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨C, hC, hbound⟩ := exists_uniform_time_one_hessian_bound_one hA
    refine ⟨C, hC, ?_⟩
    intro M _ _ _ _ _ _ g D hcomplete F u _ _ hvalue hgrad
    exact hbound g D hcomplete F u hvalue hgrad
  have hn : 2 ≤ n := by omega
  obtain ⟨r, B, H, hr, hB, hH, hlift⟩ :=
    RiemannianMetric.exists_uniform_harmonic_lift hn hK
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨C, hC, hbound⟩ := exists_uniform_hessian_bound_on_harmonic_lift
    (show 1 ≤ n by omega) hr (inv_pos.mpr hBpos)
    ((inv_le_one_of_one_le₀ hB).trans hB) hH.le hA
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g D hcomplete F u _ hsec hvalue hgrad p v w
  obtain ⟨L⟩ := hlift g D hcomplete hsec p
  have hb := hbound g D L.h L.D' L.e
    (by simpa only [mul_comm r 2] using L.he)
    (by simpa only [mul_comm r 2] using L.hlocal)
    (by simpa only [mul_comm r 2] using L.hpullback)
    (by
      simpa +instances only [mul_comm r 2, RiemannianMetric.euclideanCoefficients]
        using! L.helliptic)
    (by simpa only [mul_comm r 2] using L.hderiv)
    (by simpa only [mul_comm r 2] using L.hharmonic)
    F u hvalue hgrad
  have hep := L.he0
  rw [hep] at hb
  exact hb v w

end LeviCivitaData
end PoincareConjecture
