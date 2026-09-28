import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_regular_continued_polar_map
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {p : AnnulusCoordinates} (hp : p ∈ standardAnnulusDomain)
    {R : ℝ} (hR : 0 < R) :
    ∃ (e : AnnulusCoordinates → AnnulusCoordinates) (U : Set AnnulusCoordinates),
      IsOpen U ∧ (0 : AnnulusCoordinates) ∈ U ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U ∧
      (∀ v w : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
          (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w) ∧
      (∀ v ∈ U, ∀ w : AnnulusCoordinates,
        N.metric.pullbackCoefficients e v v w = inner ℝ v w) ∧
      (∀ v ∈ U, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ U}) ∧
      ∀ theta : AnnulusCoordinates, ‖theta‖ = 1 → ∀ b : ℝ,
        0 < b → b < R → Real.sqrt (max K 1) * b < Real.pi →
        (∀ t ∈ Icc (0 : ℝ) b, e (t • theta) ∈ standardAnnulusDomain) →
        ∀ t ∈ Icc (0 : ℝ) b, t • theta ∈ U ∧
          Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (t • theta)) ∧
          (∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
            t • theta ∈ F.source ∧ F.source ⊆ U ∧
            (F : AnnulusCoordinates → AnnulusCoordinates) = e ∧
            ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target) ∧
          ∀ radius a : ℝ, e (t • theta) = intrinsicAnnulusBoundary radius a →
            ∃ (J : Set ℝ) (u : ℝ → AnnulusCoordinates),
              IsOpen J ∧ a ∈ J ∧ ContDiffOn ℝ ∞ u J ∧ u a = t • theta ∧
              MapsTo u J U ∧ ∀ s ∈ J, e (u s) = intrinsicAnnulusBoundary radius s := by
  obtain ⟨e, U, hU, hzero, _, he0, he, hmetric, hgauss, hgeo, _, hcontains⟩ :=
    m64Intrinsic_exists_continued_radial_exponential N hp hR
  refine ⟨e, U, hU, hzero, he0, he, hmetric, hgauss, hgeo, ?_⟩
  intro theta htheta b hb hbR hbpi hmap
  have hsub (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) : s • theta ∈ U := by
    apply hcontains (s • theta)
    · simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg hs.1, htheta, mul_one] using hs.2.trans_lt hbR
    · intro t ht
      rw [smul_smul]
      exact hmap (t * s) ⟨mul_nonneg ht.1 hs.1,
        (mul_le_mul_of_nonneg_right ht.2 hs.1).trans (by simpa only [one_mul] using hs.2)⟩
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right K 1))
  have hKkappa : K ≤ Real.sqrt (max K 1) ^ 2 := by
    rw [Real.sq_sqrt (le_trans zero_le_one (le_max_right K 1))]
    exact le_max_left K 1
  have hi := m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper N K
    (Real.sqrt (max K 1)) hK hkappa hKkappa hU hzero he hgeo hmetric theta htheta
    hb hbpi hsub (fun s hs => hmap s ⟨hs.1.le, hs.2.le⟩)
  intro t ht
  refine ⟨hsub t ht, hi t ht,
    m64Intrinsic_exists_smooth_polar_inverse hU he (hsub t ht) (hi t ht), ?_⟩
  intro radius a hpoint
  exact m64Intrinsic_exists_local_lifted_boundary hU he (hsub t ht) (hi t ht) hpoint

end PoincareConjecture
