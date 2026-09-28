import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy









noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.CoordinateExponential

variable {n : ℕ}

private def metricOfCoefficients
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v) :
    RiemannianMetric n (EuclideanSpace ℝ (Fin n)) where
  inner := B
  symm := hsymm
  pos := hpos
  isVonNBounded x := by
    obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound
      (B := fun _ : EuclideanSpace ℝ (Fin n) => B x) (K := {x})
      isCompact_singleton continuousOn_const (fun _ _ => hpos x)
    change Bornology.IsVonNBounded ℝ {v : EuclideanSpace ℝ (Fin n) | B x v v < 1}
    apply (NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin n)) (c⁻¹ + 1)).subset
    intro v hv
    change B x v v < 1 at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖v‖ ^ 2 < c⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hc]
      nlinarith [hbound x (mem_singleton x) v]
    nlinarith [sq_nonneg (‖v‖ - 1 / 2)]
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    convert! hB.contDiffAt.contMDiffAt using 1
    ext y v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]



theorem exists_gauss_metric_extension
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R))
    (hsymm : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ∀ v, v ≠ 0 → 0 < B x v v)
    (hgauss : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, ∀ w,
      B x x w = inner ℝ x w) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g),
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
        g.euclideanCoefficients x = B x) ∧
      (∀ x w, g.euclideanCoefficients x x w = inner ℝ x w) := by
  let E := EuclideanSpace ℝ (Fin n)
  let f : ContDiffBump (0 : E) :=
    ⟨r, s, hr, hrs⟩
  let δ : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  let C : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun x => f x • B x + (1 - f x) • δ
  have hCa (x v w : E) :
      C x v w = f x * B x v w + (1 - f x) * inner ℝ v w := rfl
  have hfs : ContDiff ℝ ∞ (fun x : E => f x) := f.contDiff
  have hxsupport (x : E) (hx : x ∈ tsupport f) :
      x ∈ Metric.ball (0 : E) R := by
    rw [f.tsupport_eq] at hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hx hsR
  have hC : ContDiff ℝ ∞ C := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hfirst : ContDiffAt ℝ ∞ (fun y : E => f y • B y) x := by
      by_cases hx : x ∈ tsupport f
      · exact hfs.contDiffAt.smul ((hB x (hxsupport x hx)).contDiffAt
          (Metric.isOpen_ball.mem_nhds (hxsupport x hx)))
      · apply (contDiffAt_const (c := (0 : E →L[ℝ] E →L[ℝ] ℝ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [hy]
    exact hfirst.add ((contDiffAt_const.sub hfs.contDiffAt).smul contDiffAt_const)
  have hCs : ∀ x v w, C x v w = C x w v := by
    intro x v w
    rw [hCa, hCa]
    by_cases hx : f x = 0
    · simp [hx, real_inner_comm]
    · have hxU : x ∈ Metric.ball (0 : E) R :=
        hxsupport x (subset_tsupport f (Function.mem_support.mpr hx))
      rw [hsymm x hxU v w, real_inner_comm v w]
  have hCp : ∀ x v, v ≠ 0 → 0 < C x v v := by
    intro x v hv
    rw [hCa]
    by_cases hx : f x = 0
    · simpa [hx] using real_inner_self_pos.mpr hv
    · have hxU : x ∈ Metric.ball (0 : E) R :=
        hxsupport x (subset_tsupport f (Function.mem_support.mpr hx))
      have hfp : 0 < f x := lt_of_le_of_ne f.nonneg (Ne.symm hx)
      have hnonneg : 0 ≤ (1 - f x) * inner ℝ v v :=
        mul_nonneg (sub_nonneg.mpr f.le_one) real_inner_self_nonneg
      exact add_pos_of_pos_of_nonneg (mul_pos hfp (hpos x hxU v hv)) hnonneg
  let g := metricOfCoefficients C hC hCs hCp
  let D : LeviCivitaData g := g.euclideanLeviCivitaData
  refine ⟨g, D, ?_, ?_⟩
  · intro x hx
    change C x = B x
    ext v w
    rw [hCa, f.one_of_mem_closedBall hx]
    ring
  · intro x w
    change C x x w = inner ℝ x w
    rw [hCa]
    by_cases hx : f x = 0
    · simp [hx]
    · have hxU : x ∈ Metric.ball (0 : E) R :=
        hxsupport x (subset_tsupport f (Function.mem_support.mpr hx))
      rw [hgauss x hxU w]
      ring

end PoincareConjecture.CoordinateExponential
