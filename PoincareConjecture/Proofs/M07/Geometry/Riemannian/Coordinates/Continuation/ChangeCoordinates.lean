import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fderiv_bilinear_apply
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (u v w : E) :
    fderiv ℝ (fun y => B y u v) x w = fderiv ℝ B x w u v := by
  have h := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  simpa using congrArg (fun L => L w) h.fderiv

private theorem fderiv_metric_pullback
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hf : ContDiffAt ℝ ∞ f x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v))
    (a u v : E) :
    fderiv ℝ B x a u v =
      fderiv ℝ C (f x) (fderiv ℝ f x a) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        C (f x) (fderiv ℝ (fderiv ℝ f) x a u) (fderiv ℝ f x v) +
        C (f x) (fderiv ℝ f x u) (fderiv ℝ (fderiv ℝ f) x a v) := by
  have hD := (hf.fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hc := hC.hasFDerivAt.comp x (hf.differentiableAt (by simp)).hasFDerivAt
  have hd := (hc.clm_apply
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x))).clm_apply
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have heq : (fun y => B y u v) =ᶠ[𝓝 x]
      (fun y => C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) :=
    hmetric.mono fun y hy => hy u v
  rw [← fderiv_bilinear_apply hB u v a, heq.fderiv_eq]
  simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun L => L a) hd.fderiv

private theorem inner_coordinateChristoffel
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hinv : (B x).IsInvertible) (u v w : E) :
    B x (coordinateChristoffel B x u v) w =
      (2⁻¹ : ℝ) * (fderiv ℝ B x u v w + fderiv ℝ B x v w u -
        fderiv ℝ B x w u v) := by
  have h := congrArg (fun L : E →L[ℝ] ℝ => L w)
    (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B x) u v))
  simpa [coordinateChristoffel, metricKoszulCovector] using h



theorem coordinateChristoffel_change_coordinates
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C (f x))
    (hBinv : (B x).IsInvertible) (hCinv : (C (f x)).IsInvertible)
    (hCsymm : ∀ u v, C (f x) u v = C (f x) v u)
    (hf : ContDiffAt ℝ ∞ f x) (hsurj : Function.Surjective (fderiv ℝ f x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) (u : E) :
    fderiv ℝ f x (coordinateChristoffel B x u u) =
      fderiv ℝ (fderiv ℝ f) x u u +
        coordinateChristoffel C (f x) (fderiv ℝ f x u) (fderiv ℝ f x u) := by
  apply hCinv.injective
  ext z
  obtain ⟨w, rfl⟩ := hsurj z
  rw [← hmetric.self_of_nhds, inner_coordinateChristoffel hBinv]
  simp only [map_add, add_apply]
  rw [inner_coordinateChristoffel hCinv]
  rw [fderiv_metric_pullback hB hC hf hmetric,
    fderiv_metric_pullback hB hC hf hmetric,
    fderiv_metric_pullback hB hC hf hmetric]
  have hsecond := (hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    norm_cast)).eq u w
  rw [hsecond]
  rw [hCsymm (fderiv ℝ f x w), hCsymm (fderiv ℝ f x u)]
  ring



theorem hasDerivAt_geodesic_change_coordinates
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {q w : ℝ → E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (q t)) (hC : DifferentiableAt ℝ C (f (q t)))
    (hBinv : (B (q t)).IsInvertible) (hCinv : (C (f (q t))).IsInvertible)
    (hCsymm : ∀ u v, C (f (q t)) u v = C (f (q t)) v u)
    (hf : ContDiffAt ℝ ∞ f (q t))
    (hsurj : Function.Surjective (fderiv ℝ f (q t)))
    (hmetric : ∀ᶠ y in 𝓝 (q t), ∀ u v,
      B y u v = C (f y) (fderiv ℝ f y u) (fderiv ℝ f y v))
    (hq : HasDerivAt q (w t) t)
    (hw : HasDerivAt w (-coordinateChristoffel B (q t) (w t) (w t)) t) :
    HasDerivAt (fun s => f (q s)) (fderiv ℝ f (q t) (w t)) t ∧
      HasDerivAt (fun s => fderiv ℝ f (q s) (w s))
        (-coordinateChristoffel C (f (q t)) (fderiv ℝ f (q t) (w t))
          (fderiv ℝ f (q t) (w t))) t := by
  refine ⟨(hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hq, ?_⟩
  have hD := (hf.fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hd := (hD.hasFDerivAt.comp_hasDerivAt t hq).clm_apply hw
  convert! hd using 1
  simp only [Function.comp_apply, map_neg]
  rw [coordinateChristoffel_change_coordinates hB hC hBinv hCinv hCsymm hf hsurj hmetric]
  abel

end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem contDiffAt_chart_transition (p r : M) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hr : (extChartAt (𝓡 n) p).symm x ∈ (extChartAt (𝓡 n) r).source) :
    ContDiffAt ℝ ∞ (fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hr)).comp x
    ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx))

private theorem chart_coefficients_transition (g : RiemannianMetric n M) (p r : M)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hr : (extChartAt (𝓡 n) p).symm x ∈ (extChartAt (𝓡 n) r).source)
    (u v : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x u v =
      g.pullbackCoefficients (extChartAt (𝓡 n) r).symm
        (extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm x))
        (fderiv ℝ (fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)) x u)
        (fderiv ℝ (fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)) x v) := by
  let f := fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)
  have hp := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx)
  have hf := contDiffAt_chart_transition p r hx hr
  have hfr := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) r).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) r).mem_nhds
      ((extChartAt (𝓡 n) r).map_source hr))
  have heq : ((extChartAt (𝓡 n) r).symm ∘ f) =ᶠ[𝓝 x]
      (extChartAt (𝓡 n) p).symm := by
    filter_upwards [hp.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source r).mem_nhds hr)] with y hy
    exact (extChartAt (𝓡 n) r).left_inv hy
  have hderiv := mfderiv_comp x (hfr.mdifferentiableAt (by simp))
    (hf.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hderiv
  change g.inner ((extChartAt (𝓡 n) p).symm x)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x u)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x v) =
    g.inner ((extChartAt (𝓡 n) r).symm (f x))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) r).symm (f x) (fderiv ℝ f x u))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) r).symm (f x) (fderiv ℝ f x v))
  have hd (v : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x v =
        mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) r).symm (f x)
          (fderiv ℝ f x v) :=
    congrArg (fun L => L v) hderiv
  rw [hd u, hd v]
  have hpoint : (extChartAt (𝓡 n) r).symm (f x) = (extChartAt (𝓡 n) p).symm x :=
    heq.self_of_nhds
  exact congrArg (fun z : M => g.inner z
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) r).symm (f x) (fderiv ℝ f x u))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) r).symm (f x) (fderiv ℝ f x v)))
    hpoint.symm

set_option maxHeartbeats 2000000 in


theorem hasDerivAt_chart_geodesic_change_coordinates (g : RiemannianMetric n M) (p r : M)
    {q w : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (htp : q t ∈ (extChartAt (𝓡 n) p).target)
    (htr : (extChartAt (𝓡 n) p).symm (q t) ∈ (extChartAt (𝓡 n) r).source)
    (hq : HasDerivAt q (w t) t)
    (hw : HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
        (q t) (w t) (w t)) t) :
    let f := fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)
    HasDerivAt (fun s => f (q s)) (fderiv ℝ f (q t) (w t)) t ∧
      HasDerivAt (fun s => fderiv ℝ f (q s) (w s))
        (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) r).symm)
          (f (q t)) (fderiv ℝ f (q t) (w t)) (fderiv ℝ f (q t) (w t))) t := by
  let f := fun y => extChartAt (𝓡 n) r ((extChartAt (𝓡 n) p).symm y)
  have hp := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htp)
  have hmetric : ∀ᶠ y in 𝓝 (q t), ∀ u v,
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm y u v =
        g.pullbackCoefficients (extChartAt (𝓡 n) r).symm (f y)
          (fderiv ℝ f y u) (fderiv ℝ f y v) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htp,
      hp.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source r).mem_nhds htr)]
      with y hyp hyr u v
    exact chart_coefficients_transition g p r hyp hyr u v
  have hinv := g.isInvertible_chartCoefficients p htp
  have hsurj : Function.Surjective (fderiv ℝ f (q t)) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    intro u v huv
    apply hinv.injective
    ext z
    change fderiv ℝ f (q t) u = fderiv ℝ f (q t) v at huv
    rw [hmetric.self_of_nhds u z, hmetric.self_of_nhds v z, huv]
  have hrTarget := (extChartAt (𝓡 n) r).map_source htr
  exact hasDerivAt_geodesic_change_coordinates
    (((g.contDiffOn_chartCoefficients p _ htp).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htp)).differentiableAt (by simp))
    (((g.contDiffOn_chartCoefficients r _ hrTarget).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) r).mem_nhds hrTarget)).differentiableAt (by simp))
    hinv (g.isInvertible_chartCoefficients r hrTarget) (fun u v => g.symm _ _ _)
    (contDiffAt_chart_transition p r htp htr) hsurj hmetric hq hw

end PoincareConjecture.RiemannianMetric
