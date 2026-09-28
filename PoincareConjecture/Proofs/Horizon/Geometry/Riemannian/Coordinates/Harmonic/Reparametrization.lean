import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.MetricExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Inverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality










set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



lemma harmonic_coordinates_of_inverse_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hF : ContDiffOn ℝ ∞ F F.source) (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hsub : U ⊆ F.target)
    (hmetric : ∀ y ∈ U, h.euclideanCoefficients y = g.pullbackCoefficients F.symm y)
    (hharm : ∀ x ∈ F.source, ∀ i : Fin n,
      D.laplacian (fun z : EuclideanSpace ℝ (Fin n) => F z i) x = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (i : Fin n) :
    D'.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0 := by
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) F.symm y).IsInvertible := by
    filter_upwards [hU.mem_nhds hx] with y hy
    apply g.isInvertible_mfderiv_of_positive_pullback
    intro v hv
    rw [← hmetric y hy]
    exact h.pos y v hv
  have hmetric' : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      h.inner y a b = g.inner (F.symm y)
        (mfderiv (𝓡 n) (𝓡 n) F.symm y a) (mfderiv (𝓡 n) (𝓡 n) F.symm y b) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    intro a b
    exact congrArg (fun B => B a b) (hmetric y hy)
  have hFi' := (hFi.contDiffAt (F.open_target.mem_nhds (hsub hx))).contMDiffAt
  have hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun z : EuclideanSpace ℝ (Fin n) => F z i) (F.symm x) := by
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp _
      (hF.contDiffAt (F.open_source.mem_nhds (F.map_target (hsub hx))))).contMDiffAt
  have heq : (fun z : EuclideanSpace ℝ (Fin n) => z i) =ᶠ[𝓝 x]
      ((fun z : EuclideanSpace ℝ (Fin n) => F z i) ∘ F.symm) := by
    filter_upwards [F.open_target.mem_nhds (hsub hx)] with y hy
    simp only [Function.comp_apply, F.right_inv hy]
  rw [D'.laplacian_eq_of_eventuallyEq heq,
    D'.laplacian_comp_of_metric_pullback D hFi' hinv hmetric' hu]
  exact hharm _ (F.map_target (hsub hx)) i

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ}



lemma inverse_pullback_elliptic
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hF : ContDiffOn ℝ ∞ F F.source)
    (hclose : ∀ x ∈ F.source,
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ x ∈ F.source, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ b * ‖v‖ ^ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ F.target) (v : EuclideanSpace ℝ (Fin n)) :
    (4 * a / 9) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients F.symm x v v ∧
      g.pullbackCoefficients F.symm x v v ≤ (4 * b) * ‖v‖ ^ 2 := by
  have h := HarmonicCoordinates.norm_fderiv_symm_bounds F hF hclose hx v
  have hl : (4 / 9 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F.symm x v‖ ^ 2 := by
    nlinarith [sq_nonneg (‖fderiv ℝ F.symm x v‖ - (2 / 3 : ℝ) * ‖v‖),
      mul_nonneg (sub_nonneg.mpr h.1) (norm_nonneg v)]
  have hu : ‖fderiv ℝ F.symm x v‖ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2)
      (add_nonneg (norm_nonneg (fderiv ℝ F.symm x v))
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (norm_nonneg v)))]
  have hg := hbound (F.symm x) (F.map_target hx) (fderiv ℝ F.symm x v)
  have hval : g.pullbackCoefficients F.symm x v v = g.inner (F.symm x)
      (fderiv ℝ F.symm x v) (fderiv ℝ F.symm x v) := by
    change g.inner _ (mfderiv _ _ _ _ _) (mfderiv _ _ _ _ _) = _
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hval]
  constructor
  · calc
      _ = a * ((4 / 9 : ℝ) * ‖v‖ ^ 2) := by ring
      _ ≤ a * ‖fderiv ℝ F.symm x v‖ ^ 2 := mul_le_mul_of_nonneg_left hl ha
      _ ≤ _ := hg.1
  · calc
      _ ≤ b * ‖fderiv ℝ F.symm x v‖ ^ 2 := hg.2
      _ ≤ b * (4 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hu hb
      _ = _ := by ring

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.HarmonicCoordinates

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} [NeZero n]



lemma exists_metric_of_harmonic_map
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {R a b : ℝ}
    (hR : 0 < R) (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R)) (hf0 : f 0 = 0)
    (hclose : ∀ x ∈ Metric.ball 0 R,
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2)
    (hbound : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hharm : ∀ x ∈ Metric.ball 0 R, ∀ i : Fin n,
      D.laplacian (fun z : EuclideanSpace ℝ (Fin n) => f z i) x = 0) :
    ∃ F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      ∃ (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D' : LeviCivitaData h),
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = f ∧
        F.source = Metric.ball 0 R ∧ Metric.ball 0 (R / 4) ⊆ F.target ∧
        ContDiffOn ℝ ∞ F.symm F.target ∧ F.symm 0 = 0 ∧
        (∀ x ∈ Metric.ball 0 (R / 8), h.euclideanCoefficients x = g.pullbackCoefficients F.symm x) ∧
        (∀ x (v : EuclideanSpace ℝ (Fin n)),
          (4 * a / 9) * ‖v‖ ^ 2 ≤ h.inner x v v ∧ h.inner x v v ≤ (4 * b) * ‖v‖ ^ 2) ∧
        ∀ x ∈ Metric.ball 0 (R / 8), ∀ i : Fin n,
          D'.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0 := by
  obtain ⟨F, hFeq, hsource, hball, hFi, hFi0⟩ := exists_inverse_on_ball hR hf hf0 hclose
  have hF : ContDiffOn ℝ ∞ F F.source := by simpa only [hFeq, hsource] using hf
  have hclose' : ∀ x ∈ F.source,
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2 := by
    simpa only [hFeq, hsource] using hclose
  have hbound' : ∀ x ∈ F.source, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ b * ‖v‖ ^ 2 := by
    simpa only [hsource] using hbound
  have hB : ContDiffOn ℝ ∞ (g.pullbackCoefficients F.symm) (Metric.ball 0 (R / 4)) := by
    intro x hx
    exact (g.contDiffAt_pullbackCoefficients
      (hFi.contDiffAt (F.open_target.mem_nhds (hball hx))).contMDiffAt).contDiffWithinAt
  have hsymm : ∀ x ∈ Metric.ball 0 (R / 4), ∀ v w,
      g.pullbackCoefficients F.symm x v w = g.pullbackCoefficients F.symm x w v := by
    intro x _ v w
    exact g.symm _ _ _
  have hbounds : ∀ x ∈ Metric.ball 0 (R / 4), ∀ v,
      (4 * a / 9) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients F.symm x v v ∧
        g.pullbackCoefficients F.symm x v v ≤ (4 * b) * ‖v‖ ^ 2 := by
    intro x hx v
    exact g.inverse_pullback_elliptic F hF hclose' ha.le (by linarith) hbound' (hball hx) v
  obtain ⟨h, heq, hglobal⟩ := RiemannianMetric.exists_extension_on_ball
    (by positivity : 0 < R / 8) (by linarith : R / 8 < R / 4)
    (by positivity : 0 < 4 * a / 9) (by linarith : 4 * a / 9 ≤ 1)
    (by linarith : 1 ≤ 4 * b) (g.pullbackCoefficients F.symm) hB hsymm hbounds
  refine ⟨F, h, h.euclideanLeviCivitaData, hFeq, hsource, hball, hFi, hFi0, heq, hglobal, ?_⟩
  intro x hx i
  apply D.harmonic_coordinates_of_inverse_pullback h.euclideanLeviCivitaData F hF hFi
    Metric.isOpen_ball ((Metric.ball_subset_ball (by linarith : R / 8 ≤ R / 4)).trans hball)
    heq _ hx i
  simpa only [hFeq, hsource] using hharm

end PoincareConjecture.HarmonicCoordinates
