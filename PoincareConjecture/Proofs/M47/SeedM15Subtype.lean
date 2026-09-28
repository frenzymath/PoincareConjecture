import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeImage
import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem seedM15_subtype_ball_image
    (U : TopologicalSpace.Opens M) (g : RiemannianMetric 3 U) (h : RiemannianMetric 3 M)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = h.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w))
    (x : U) (r : ℝ) :
    Subtype.val '' g.ball x r ⊆ h.ball x.val r := by
  apply g.image_ball_subset_ball_of_tangentNorm_le_on_open h Subtype.val isOpen_univ
    ((contMDiff_subtype_val (n := ∞)).of_le (by simp)).contMDiffOn zero_lt_one
    (fun y _hy v => ?_) (subset_univ _) (by simp)
  have hnorm := congrArg Real.sqrt (hmetric y v v)
  change h.tangentNorm y.val _ ≤ 1 * g.tangentNorm y v
  rw [one_mul]
  exact hnorm.symm.le

variable [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]




theorem seedM15_subtype_ball_volume
    (U : TopologicalSpace.Opens M) (g : RiemannianMetric 3 U) (h : RiemannianMetric 3 M)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = h.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w))
    (x : U) (r : ℝ) :
    calibratedMetricVolume g (g.ball x r) ≤ calibratedMetricVolume h (h.ball x.val r) := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  have he : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source :=
    ((contMDiff_subtype_val (n := ∞)).of_le (by simp)).contMDiffOn
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
    intro p hp
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target p).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hp
    intro q hq
    exact e.right_inv hq
  have hnorm (y : U) (v : TangentSpace (𝓡 3) y) :
      g.tangentNorm y v = h.tangentNorm (e y) (mfderiv (𝓡 3) (𝓡 3) e y v) :=
    congrArg Real.sqrt (hmetric y v v)
  have hvol := M34.calibrated_ball_volume_le_mul_of_tangent_bounds g h e he
    (hi.of_le (by simp))
    (K := 1) (L := 1) zero_lt_one zero_lt_one
    (fun y _hy v => by rw [← hnorm, one_mul])
    (fun y _hy v => by rw [hnorm, one_mul])
    (show g.ball x r ⊆ e.source from subset_univ _) (by simp : 1 * r ≤ r)
  simpa only [ENNReal.ofReal_one, one_pow, one_mul, e,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] using hvol

end PoincareConjecture.M47
