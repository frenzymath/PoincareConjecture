import PoincareConjecture.Proofs.M01.NormalizationVolume











set_option autoImplicit false

open Bundle Manifold Metric Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

universe u

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem m01_edist_image_le_pathELength [IsManifold I 1 M]
    {f : M → F} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f U) (C : ℝ≥0)
    (hC : ∀ y ∈ U,
      letI := normedAddCommGroupTangentSpaceVectorSpace (f y)
      letI := normedSpaceTangentSpaceVectorSpace (f y)
      letI : SeminormedAddCommGroup
          (TangentSpace I y →L[ℝ] TangentSpace 𝓘(ℝ, F) (f y)) :=
        ContinuousLinearMap.toSeminormedAddCommGroup
      ‖mfderiv I 𝓘(ℝ, F) f y‖ₑ ≤ C)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hrange : Icc 0 1 ⊆ γ ⁻¹' U) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 := by
  let (z : ℝ) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, ℝ) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  let (z : ℝ) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, ℝ) z) :=
    normedSpaceTangentSpaceVectorSpace z
  let (z : F) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, F) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  let (z : F) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, F) z) :=
    normedSpaceTangentSpaceVectorSpace z
  let (y : M) (z : F) : SeminormedAddCommGroup
      (TangentSpace I y →L[ℝ] TangentSpace 𝓘(ℝ, F) z) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let η := f ∘ γ
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp hγ hrange)
  change edist (η 0) (η 1) ≤ _
  rw [edist_comm (η 0) (η 1), edist_eq_enorm_sub]
  calc
    ‖η 1 - η 0‖ₑ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη zero_le_one
    _ = ∫⁻ t in Icc 0 1, ‖mfderiv[Icc 0 1] η t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, C * ‖mfderiv[Icc 0 1] γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hderiv : mfderiv[Icc 0 1] η t =
          (mfderiv I 𝓘(ℝ, F) f (γ t)) ∘L (mfderiv[Icc 0 1] γ t) := by
        apply mfderiv_comp_mfderivWithin
        · exact (hf.mdifferentiableOn one_ne_zero (γ t) (hrange ht)).mdifferentiableAt
            (hU.mem_nhds (hrange ht))
        · exact hγ.mdifferentiableOn one_ne_zero t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have happly : mfderiv[Icc 0 1] η t 1 =
          (mfderiv I 𝓘(ℝ, F) f (γ t)) (mfderiv[Icc 0 1] γ t 1) := congr($hderiv 1)
      rw [happly]
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      exact hC _ (hrange ht)
    _ = C * pathELength I γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

theorem m01_riemannianEDist_le_of_mfderiv_bound_convex [IsManifold I 1 M]
    {f : F → M} {U s : Set F}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, F) I 1 f U)
    (hs : Convex ℝ s) (hsub : s ⊆ U) (C : ℝ≥0)
    (hC : ∀ z ∈ s,
      letI := normedAddCommGroupTangentSpaceVectorSpace z
      letI := normedSpaceTangentSpaceVectorSpace z
      letI : SeminormedAddCommGroup
          (TangentSpace 𝓘(ℝ, F) z →L[ℝ] TangentSpace I (f z)) :=
        ContinuousLinearMap.toSeminormedAddCommGroup
      ‖mfderiv 𝓘(ℝ, F) I f z‖ₑ ≤ C)
    {a b : F} (ha : a ∈ s) (hb : b ∈ s) :
    riemannianEDist I (f a) (f b) ≤ C * edist a b := by
  let (z : ℝ) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, ℝ) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  let (z : ℝ) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, ℝ) z) :=
    normedSpaceTangentSpaceVectorSpace z
  let (z : F) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, F) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  let (z : F) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, F) z) :=
    normedSpaceTangentSpaceVectorSpace z
  let (z : F) (y : M) : SeminormedAddCommGroup
      (TangentSpace 𝓘(ℝ, F) z →L[ℝ] TangentSpace I y) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let η := ContinuousAffineMap.lineMap (R := ℝ) a b
  let γ := f ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' s := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact hs.segment_subset ha hb
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hlength : riemannianEDist I (f a) (f b) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact hf.comp η_smooth (hη.trans (preimage_mono hsub))
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  apply hlength.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have hderiv : mfderiv[Icc 0 1] γ t =
      (mfderiv 𝓘(ℝ, F) I f (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderiv_comp_mfderivWithin
    · exact (hf.mdifferentiableOn one_ne_zero _ (hsub (hη ht))).mdifferentiableAt
        (hU.mem_nhds (hsub (hη ht)))
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have happly : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv 𝓘(ℝ, F) I f (η t)) (mfderiv[Icc 0 1] η t 1) := congr($hderiv 1)
  rw [happly]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact hC _ (hη ht)
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_rfl

section

variable {N : Type*} [EMetricSpace N] [ChartedSpace H N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I x)] [IsManifold I 1 N]
  [IsRiemannianManifold I N]

theorem m01_lipschitzOnWith_of_mfderiv_bound_ball {f : N → F} {U : Set N}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f U)
    (C : ℝ≥0) (hCpos : 0 < C)
    (hC : ∀ y ∈ U,
      letI := normedAddCommGroupTangentSpaceVectorSpace (f y)
      letI := normedSpaceTangentSpaceVectorSpace (f y)
      letI : SeminormedAddCommGroup
          (TangentSpace I y →L[ℝ] TangentSpace 𝓘(ℝ, F) (f y)) :=
        ContinuousLinearMap.toSeminormedAddCommGroup
      ‖mfderiv I 𝓘(ℝ, F) f y‖ₑ ≤ C)
    (x : N) (δ : ℝ≥0) (_hδ : 0 < δ) (hball : Metric.eball x (3 * δ) ⊆ U) :
    LipschitzOnWith C f (Metric.eball x δ) := by
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hCpos.ne'
  intro a ha b hb
  have hxa : edist x a < (δ : ℝ≥0∞) := by simpa only [Metric.mem_eball', edist_comm] using ha
  have hxb : edist x b < (δ : ℝ≥0∞) := by simpa only [Metric.mem_eball', edist_comm] using hb
  have hab : edist a b < 2 * (δ : ℝ≥0∞) := by
    apply (edist_triangle a x b).trans_lt
    simpa only [edist_comm a x, two_mul] using ENNReal.add_lt_add hxa hxb
  rw [mul_comm (C : ℝ≥0∞)]
  apply (ENNReal.div_le_iff_le_mul (Or.inl hCne) (Or.inl ENNReal.coe_ne_top)).mp
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hmin : riemannianEDist I a b < min r (2 * (δ : ℝ≥0∞)) := by
    rw [← IsRiemannianManifold.out a b]
    exact lt_min hr hab
  obtain ⟨γ, hγa, hγb, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hmin
  have hlen : pathELength I γ 0 1 < 2 * (δ : ℝ≥0∞) := hlength.trans_le (min_le_right _ _)
  have hrange : Icc 0 1 ⊆ γ ⁻¹' U := by
    intro t ht
    apply hball
    have hpart : edist a (γ t) ≤ pathELength I γ 0 1 := by
      rw [IsRiemannianManifold.out (I := I) a (γ t)]
      apply (riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγa rfl ht.1).trans
      exact pathELength_mono le_rfl ht.2
    have hdist : edist x (γ t) < 3 * (δ : ℝ≥0∞) := by
      apply (edist_triangle x a (γ t)).trans_lt
      have := ENNReal.add_lt_add hxa (hpart.trans_lt hlen)
      simpa only [show (3 : ℝ≥0∞) = 1 + 2 by norm_num, add_mul, one_mul] using this
    simpa only [Metric.mem_eball', edist_comm] using hdist
  have himage := m01_edist_image_le_pathELength hU hf C hC hγ hrange
  rw [hγa, hγb] at himage
  have hdiv : edist (f a) (f b) / C ≤ pathELength I γ 0 1 :=
    (ENNReal.div_le_iff_le_mul (Or.inl hCne) (Or.inl ENNReal.coe_ne_top)).mpr
      (by simpa only [mul_comm] using himage)
  exact hdiv.trans (hlength.le.trans (min_le_left _ _))

end

end PoincareConjecture
