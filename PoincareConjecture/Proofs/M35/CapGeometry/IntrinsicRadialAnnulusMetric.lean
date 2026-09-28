import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialPatch
import PoincareConjecture.Proofs.M35.CapGeometry.RadialAnnulusMetric











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)



theorem intrinsicRadialAnnulusPatch_pullback (q₀ : UnitTwoSphere) (a b length : ℝ)
    (hb : 0 < b) (hl : 0 < length) (hinner : 0 < a - b * length)
    (z : StandardCylinderSpace) (hz : z.2 ∈ Ioo (-length) length)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback g
      (intrinsicRadialAnnulusPatch g hrotation hcomplete q₀ a b length
        hb hl hinner).coordinate z v w =
      intrinsicWarpingRadius g hrotation hcomplete (a + b * z.2) ^ 2 *
        inner ℝ
          (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 v.1)
          (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 w.1) +
        b ^ 2 * v.2 * w.2 := by
  let F := intrinsicSpatialDiffeomorph g hrotation hcomplete
  let N := radialAnnulusPatch q₀ a b length hb hl hinner
  have hcoord := N.coordinate_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ z.1, hz⟩)
  have hchain := mfderiv_comp z
    (F.symm.contMDiff.mdifferentiable (by simp) (N.coordinate z))
    (hcoord.mdifferentiableAt (by simp))
  have hmetric : roundCylinderPullback g (F.symm ∘ N.coordinate) z v w =
      roundCylinderPullback (intrinsicSpatialMetric g hrotation hcomplete)
        N.coordinate z v w := by
    change g.inner (F.symm (N.coordinate z))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (F.symm ∘ N.coordinate) z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (F.symm ∘ N.coordinate) z w) = _
    rw [hchain]
    change g.inner (intrinsicSpatialInverse g hrotation hcomplete (N.coordinate z))
      (mfderiv (𝓡 3) (𝓡 3) (intrinsicSpatialInverse g hrotation hcomplete)
        (N.coordinate z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate z v))
      (mfderiv (𝓡 3) (𝓡 3) (intrinsicSpatialInverse g hrotation hcomplete)
        (N.coordinate z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate z w)) = _
    rw [mfderiv_eq_fderiv]
    exact (intrinsicSpatialMetric_pullback g hrotation hcomplete _ _ _).symm
  have hr : 0 < a + b * z.2 := by
    have h := mul_lt_mul_of_pos_left hz.1 hb
    linarith
  exact hmetric.trans (intrinsic_radial_annulus_pullback g hrotation hcomplete a b z hr v w)

end PoincareConjecture.M35.Uniqueness
