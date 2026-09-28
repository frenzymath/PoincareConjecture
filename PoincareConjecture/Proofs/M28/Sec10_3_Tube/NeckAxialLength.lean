import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompetitors
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckLengthComparison
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem coordinate_path_axial_displacement_le_of_speed (N : EpsilonNeck g)
    {c : ℝ} (hc : 0 ≤ c)
    (hspeed : ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ v : RoundCylinderCoordinates,
        c * |v.2| ≤ g.tangentNorm (N.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v))
    {η : ℝ → RoundCylinderSpace}
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1 η (Icc (0 : ℝ) 1))
    (hηN : MapsTo η (Icc (0 : ℝ) 1) (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)) :
    ENNReal.ofReal (c * |(η 1).2 - (η 0).2|) ≤
      g.pathELength (N.coordinate_map ∘ η) 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (x : M) (v : TangentSpace (𝓡 3) x) :
      ENNReal.ofReal (g.tangentNorm x v) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have huniq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc zero_lt_one t ht
  have hscalar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      derivWithin (fun u => (η u).2) (Icc (0 : ℝ) 1) t =
        (mfderivWithin 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          η (Icc (0 : ℝ) 1) t 1).2 := by
    rw [← fderivWithin_derivWithin, ← mfderivWithin_eq_fderivWithin]
    change mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Prod.snd ∘ η)
      (Icc (0 : ℝ) 1) t 1 = _
    rw [mfderiv_comp_mfderivWithin t mdifferentiableAt_snd
      (hη.mdifferentiableOn one_ne_zero t ht) (huniq t ht), mfderiv_snd]
    rfl
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      mfderivWithin 𝓘(ℝ, ℝ) (𝓡 3) (N.coordinate_map ∘ η)
          (Icc (0 : ℝ) 1) t 1 =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
            η (Icc (0 : ℝ) 1) t 1) := by
    have hcoord : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (η t) :=
      ((N.coordinate_map_smooth (η t) (hηN ht)).contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds (hηN ht))).mdifferentiableAt (by simp)
    rw [mfderiv_comp_mfderivWithin t hcoord
      (hη.mdifferentiableOn one_ne_zero t ht) (huniq t ht)]
    rfl
  have hdisplacement := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
    (contMDiffOn_iff_contDiffOn.mp (contMDiff_snd.comp_contMDiffOn hη)) zero_le_one
  calc
    ENNReal.ofReal (c * |(η 1).2 - (η 0).2|) =
        ENNReal.ofReal c * ‖(η 1).2 - (η 0).2‖ₑ := by
      rw [ENNReal.ofReal_mul hc, Real.enorm_eq_ofReal_abs]
    _ ≤ ENNReal.ofReal c *
        ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin (fun u => (η u).2) (Icc (0 : ℝ) 1) t‖ₑ :=
      mul_le_mul_right hdisplacement _
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal c *
          ‖derivWithin (fun u => (η u).2) (Icc (0 : ℝ) 1) t‖ₑ :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        ‖mfderivWithin 𝓘(ℝ, ℝ) (𝓡 3) (N.coordinate_map ∘ η)
          (Icc (0 : ℝ) 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [Real.enorm_eq_ofReal_abs, hscalar t ht, ← ENNReal.ofReal_mul hc,
        ← hnorm, hderiv t ht]
      apply ENNReal.ofReal_le_ofReal
      exact hspeed (η t) (hηN ht).2 _
    _ = g.pathELength (N.coordinate_map ∘ η) 0 1 := by
      symm
      exact Manifold.pathELength_eq_lintegral_mfderivWithin_Icc



theorem coordinate_path_axial_displacement_le (N : EpsilonNeck g)
    {η : ℝ → RoundCylinderSpace}
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1 η (Icc (0 : ℝ) 1))
    (hηN : MapsTo η (Icc (0 : ℝ) 1) (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)) :
    ENNReal.ofReal ((N.scale / 2) * |(η 1).2 - (η 0).2|) ≤
      g.pathELength (N.coordinate_map ∘ η) 0 1 :=
  coordinate_path_axial_displacement_le_of_speed N
    (div_nonneg N.scale_pos.le (by norm_num)) N.coordinate_axial_speed_lower hη hηN



theorem path_axial_displacement_le_of_speed (N : EpsilonNeck g)
    {c : ℝ} (hc : 0 ≤ c)
    (hspeed : ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ v : RoundCylinderCoordinates,
        c * |v.2| ≤ g.tangentNorm (N.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v))
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγN : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal (c *
      |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) ≤
        g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨σ, h0, h1, hσ, hσN, hσlen⟩ :=
    exists_unit_interval_path g hab hγ hγN
  let η := N.coordinate_inverse ∘ σ
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1 η (Icc (0 : ℝ) 1) :=
    (N.coordinate_inverse_smooth.of_le (by simp)).comp hσ hσN
  have hηN : MapsTo η (Icc (0 : ℝ) 1)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    fun t ht => N.coordinate_inverse_mem (σ t) (hσN ht)
  have hcancel : EqOn (N.coordinate_map ∘ η) σ (Icc (0 : ℝ) 1) :=
    fun _ ht => N.coordinate_map_coordinate_inverse (hσN ht)
  have hlength : g.pathELength (N.coordinate_map ∘ η) 0 1 = g.pathELength σ 0 1 :=
    Manifold.pathELength_congr hcancel
  have hbound := coordinate_path_axial_displacement_le_of_speed N hc hspeed hη hηN
  rw [hlength, hσlen] at hbound
  simpa only [η, Function.comp_apply, h0, h1] using hbound



theorem path_axial_displacement_le (N : EpsilonNeck g)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγN : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal ((N.scale / 2) *
      |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) ≤
        g.pathELength γ a b :=
  path_axial_displacement_le_of_speed N
    (div_nonneg N.scale_pos.le (by norm_num)) N.coordinate_axial_speed_lower hab hγ hγN

end PoincareConjecture.M28
