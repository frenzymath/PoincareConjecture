import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.EuclideanConstruction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension











noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ}

section Differential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace


lemma isInvertible_mfderiv_of_positive_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)}
    (hpos : ∀ v, v ≠ 0 → 0 < g.pullbackCoefficients e x v v) :
    (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) e x
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    by_contra hne
    have hp := hpos v hne
    change 0 < g.inner (e x) (A v) (A v) at hp
    rw [hv, map_zero] at hp
    exact (lt_irrefl 0) hp
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

end Differential

private def ofUniformlyPositiveCoefficients
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ x v w, B x v w = B x w v)
    {a : ℝ} (ha : 0 < a) (hlower : ∀ x v, a * ‖v‖ ^ 2 ≤ B x v v) :
    RiemannianMetric n (EuclideanSpace ℝ (Fin n)) where
  inner := B
  symm := hsymm
  pos x v hv := (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hlower x v)
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : EuclideanSpace ℝ (Fin n) | B x v v < 1}
    apply (NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin n)) (a⁻¹ + 1)).subset
    intro v hv
    change B x v v < 1 at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖v‖ ^ 2 < a⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ ha]
      nlinarith [hlower x v]
    nlinarith [sq_nonneg (‖v‖ - 1 / 2)]
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    convert! hB.contDiffAt.contMDiffAt using 1
    ext y v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]



lemma exists_extension_on_ball
    {r R a b : ℝ} (hr : 0 < r) (hrR : r < R)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Metric.ball 0 R))
    (hsymm : ∀ x ∈ Metric.ball 0 R, ∀ v w, B x v w = B x w v)
    (hbound : ∀ x ∈ Metric.ball 0 R, ∀ v,
      a * ‖v‖ ^ 2 ≤ B x v v ∧ B x v v ≤ b * ‖v‖ ^ 2) :
    ∃ h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ Metric.ball 0 r, h.euclideanCoefficients x = B x) ∧
      ∀ x v, a * ‖v‖ ^ 2 ≤ h.euclideanCoefficients x v v ∧
        h.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2 := by
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨r, (r + R) / 2, hr, by linarith⟩
  let δ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  let A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun x => f x • B x + (1 - f x) • δ
  have hAapply (x v w : EuclideanSpace ℝ (Fin n)) :
      A x v w = f x * B x v w + (1 - f x) * inner ℝ v w := rfl
  have hsupport : tsupport f ⊆ Metric.ball 0 R := by
    rw [f.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [f]; linarith)
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hfirst : ContDiffAt ℝ ∞ (fun y => f y • B y) x := by
      by_cases hx : x ∈ tsupport f
      · exact f.contDiff.contDiffAt.smul
          (hB.contDiffAt (Metric.isOpen_ball.mem_nhds (hsupport hx)))
      · apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [hy]
    exact hfirst.add ((contDiffAt_const.sub f.contDiff.contDiffAt).smul contDiffAt_const)
  have hAsymm : ∀ x v w, A x v w = A x w v := by
    intro x v w
    rw [hAapply, hAapply]
    by_cases hx : f x = 0
    · simp [hx, real_inner_comm]
    · rw [hsymm x (hsupport (subset_tsupport f (Function.mem_support.mpr hx))) v w,
        real_inner_comm v w]
  have hAbound : ∀ x v, a * ‖v‖ ^ 2 ≤ A x v v ∧ A x v v ≤ b * ‖v‖ ^ 2 := by
    intro x v
    rw [hAapply, real_inner_self_eq_norm_sq]
    have hfl : 0 ≤ f x := f.nonneg
    have hfu : 0 ≤ 1 - f x := sub_nonneg.mpr f.le_one
    have hal := mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖v‖)
    have hbu := mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖v‖)
    by_cases hx : f x = 0
    · simpa [hx] using And.intro hal hbu
    · obtain ⟨hl, hu⟩ := hbound x (hsupport (subset_tsupport f (Function.mem_support.mpr hx))) v
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hl hfl,
          mul_le_mul_of_nonneg_left hal hfu]
      · nlinarith [mul_le_mul_of_nonneg_left hu hfl,
          mul_le_mul_of_nonneg_left hbu hfu]
  let h := ofUniformlyPositiveCoefficients A hA hAsymm ha (fun x v => (hAbound x v).1)
  refine ⟨h, ?_, hAbound⟩
  intro x hx
  have hf : f x = 1 := f.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  change A x = B x
  simp only [A, hf, one_smul, sub_self, zero_smul, add_zero]

end PoincareConjecture.RiemannianMetric
