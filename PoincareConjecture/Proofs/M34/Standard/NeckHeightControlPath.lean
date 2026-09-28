import PoincareConjecture.Proofs.M34.Standard.NeckHeightControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

theorem scalar_displacement_le_pathELength
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {γ : ℝ → M} {η : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 η (Icc a b))
    (hbound : ∀ t ∈ Ioo a b,
      (abs : ℝ → ℝ) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) η t 1) ≤
        C * g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) :
    ENNReal.ofReal |η b - η a| ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  have hd : EDist.edist (η a) (η b) ≤ Manifold.pathELength 𝓘(ℝ, ℝ) η a b := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ))]
    exact Manifold.riemannianEDist_le_pathELength hη rfl rfl hab
  have hscalar : ENNReal.ofReal |η b - η a| = EDist.edist (η a) (η b) := by
    rw [edist_comm, edist_eq_enorm_sub, Real.enorm_eq_ofReal_abs]
  rw [hscalar]
  apply hd.trans
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    g.pathELength_eq_lintegral_tangentNorm, ← restrict_Ioo_eq_restrict_Icc,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  rw [enorm_tangentSpace_vectorSpace, Real.enorm_eq_ofReal_abs]
  exact (ENNReal.ofReal_le_ofReal (hbound t ht)).trans_eq (ENNReal.ofReal_mul hC)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem height_displacement_le_pathELength
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hmem : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2| ≤
      ENNReal.ofReal (2 / N.scale) * g.pathELength γ a b := by
  have hi : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1
      (N.coordinate_inverse ∘ γ) (Icc a b) :=
    (N.coordinate_inverse_smooth.of_le (by simp)).comp hγ hmem
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (Prod.snd ∘ (N.coordinate_inverse ∘ γ)) (Icc a b) :=
    contMDiff_snd.comp_contMDiffOn hi
  apply g.scalar_displacement_le_pathELength hab (div_nonneg (by norm_num) N.scale_pos.le) hη
  intro t ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hγd := ((hγ t ht').contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by simp)
  have hid := ((N.coordinate_inverse_smooth (γ t) (hmem ht')).contMDiffAt
    (N.carrier_open.mem_nhds (hmem ht'))).mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply t mdifferentiableAt_snd (hid.comp t hγd), mfderiv_snd]
  change |(mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (N.coordinate_inverse ∘ γ) t 1).2| ≤ _
  rw [mfderiv_comp_apply t hid hγd]
  exact N.coordinate_inverse_axial_le_tangentNorm (hmem ht') _

end PoincareConjecture.EpsilonNeck
