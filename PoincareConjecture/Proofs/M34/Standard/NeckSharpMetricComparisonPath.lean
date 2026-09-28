import PoincareConjecture.Proofs.M34.Standard.NeckSharpMetricComparison
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlPath
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem height_displacement_le_pathELength_of_axial_speed
    {A : ℝ} (hA : 0 ≤ A)
    (hspeed : ∀ x ∈ N.carrier, ∀ v : TangentSpace (𝓡 3) x,
      |(mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v).2| ≤
        A * g.tangentNorm x v)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hmem : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2| ≤
      ENNReal.ofReal A * g.pathELength γ a b := by
  have hi : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1
      (N.coordinate_inverse ∘ γ) (Icc a b) :=
    (N.coordinate_inverse_smooth.of_le (by simp)).comp hγ hmem
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (Prod.snd ∘ (N.coordinate_inverse ∘ γ)) (Icc a b) :=
    contMDiff_snd.comp_contMDiffOn hi
  apply g.scalar_displacement_le_pathELength hab hA hη
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
  exact hspeed (γ t) (hmem ht') _



theorem axialPath_height_mem {z t : ℝ}
    (hz : z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have h := convex_Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ hzero hz
    (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  simpa only [smul_eq_mul, mul_zero, zero_add] using h



theorem axialPath_contMDiffOn (q : UnitTwoSphere) {z : ℝ}
    (hz : z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun t : ℝ => N.coordinate_map (q, t * z)) (Icc (0 : ℝ) 1) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => t * z) := contDiff_id.mul contDiff_const
  apply N.coordinate_map_smooth.comp
    ((contMDiff_const.prodMk hs.contMDiff).contMDiffOn)
  intro t ht
  exact ⟨mem_univ _, N.axialPath_height_mem hz ht⟩



theorem axialPath_pathELength_le_sharp (he : N.epsilon ≤ 1 / 8)
    (q : UnitTwoSphere) {z : ℝ} (hz : z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    g.pathELength (fun t : ℝ => N.coordinate_map (q, t * z)) 0 1 ≤
      ENNReal.ofReal ((5 / 4 : ℝ) * N.scale * |z|) := by
  let η : ℝ → RoundCylinderSpace := fun t => (q, t * z)
  have hs : ContDiff ℝ ∞ (fun t : ℝ => t * z) := contDiff_id.mul contDiff_const
  have hη : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ η :=
    contMDiff_const.prodMk hs.contMDiff
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (N.coordinate_map (η t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (N.coordinate_map ∘ η) t 1) ≤
      (5 / 4 : ℝ) * N.scale * |z| := by
    have htN := N.axialPath_height_mem hz ht
    have hm := ((N.coordinate_map_smooth (η t) ⟨mem_univ _, htN⟩).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, htN⟩)).mdifferentiableAt
        (by simp)
    have hdt : mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t 1 = (0, z) := by
      have hd : HasDerivAt (fun u : ℝ => u * z) z t := by
        convert! (hasDerivAt_id t).mul_const z using 1
        simp
      have hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) (fun _ : ℝ => q) t :=
        mdifferentiableAt_const
      change mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (fun t : ℝ => (q, t * z)) t 1 = _
      rw [mfderiv_prodMk hc hd.differentiableAt.mdifferentiableAt, mfderiv_const,
        mfderiv_eq_fderiv]
      change (0, fderiv ℝ (fun u : ℝ => u * z) t 1) = (0, z)
      rw [hd.hasFDerivAt.fderiv]
      simp
    rw [mfderiv_comp_apply t hm (hη.mdifferentiableAt (by simp)), hdt]
    exact N.coordinate_map_axial_tangentNorm_le_sharp he htN z
  rw [g.pathELength_eq_lintegral_tangentNorm]
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal ((5 / 4 : ℝ) * N.scale * |z|) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact ENNReal.ofReal_le_ofReal (hspeed t ht)
    _ = _ := by simp

end PoincareConjecture.EpsilonNeck
