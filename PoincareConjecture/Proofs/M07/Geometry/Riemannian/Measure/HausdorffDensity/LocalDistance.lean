import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ChartSegment









set_option autoImplicit false

open Set MeasureTheory Manifold Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in

theorem edist_le_mul_pathELength_of_mfderiv_le
    {f : M → F} {s : Set M}
    (hf : ∀ z ∈ s, ContMDiffAt I (𝓘(ℝ, F)) 1 f z)
    {K : ℝ≥0} (hK : ∀ z ∈ s, ‖mfderiv I (𝓘(ℝ, F)) f z‖ₑ ≤ K)
    {γ : ℝ → M} (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc 0 1))
    (hγs : MapsTo γ (Icc 0 1) s) :
    edist (f (γ 0)) (f (γ 1)) ≤ (K : ℝ≥0∞) * pathELength I γ 0 1 := by
  let η := f ∘ γ
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, F)) 1 η (Icc 0 1) :=
    (show ContMDiffOn I (𝓘(ℝ, F)) 1 f s from
      fun z hz ↦ (hf z hz).contMDiffWithinAt).comp hγ hγs
  calc
    edist (f (γ 0)) (f (γ 1)) = ‖η 1 - η 0‖ₑ := by
      rw [edist_comm, edist_eq_enorm_sub]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
        (contMDiffOn_iff_contDiffOn.mp hη) zero_le_one
    _ = ∫⁻ t in Icc 0 1, ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, F)) η (Icc 0 1) t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, (K : ℝ≥0∞) * ‖mfderivWithin (𝓘(ℝ, ℝ)) I γ (Icc 0 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
      have hchain : mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, F)) η (Icc 0 1) t =
          (mfderiv I (𝓘(ℝ, F)) f (γ t)) ∘L
            (mfderivWithin (𝓘(ℝ, ℝ)) I γ (Icc 0 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact (hf _ (hγs ht)).mdifferentiableAt one_ne_zero
        · exact hγ.mdifferentiableOn one_ne_zero _ ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one _ ht
      have hchain1 : mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, F)) η (Icc 0 1) t 1 =
          (mfderiv I (𝓘(ℝ, F)) f (γ t))
            (mfderivWithin (𝓘(ℝ, ℝ)) I γ (Icc 0 1) t 1) := congr($hchain 1)
      rw [hchain1]
      exact (ContinuousLinearMap.le_opENorm _ _).trans
        (by gcongr; exact hK _ (hγs ht))
    _ = (K : ℝ≥0∞) * pathELength I γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

set_option backward.isDefEq.respectTransparency false in


theorem edist_le_mul_riemannianEDist_of_mfderiv_le_on_ball
    {f : M → F} {p : M} {r K : ℝ≥0} (hK : 0 < K)
    (hf : ∀ z, riemannianEDist I p z < 3 * (r : ℝ≥0∞) →
      ContMDiffAt I (𝓘(ℝ, F)) 1 f z)
    (hbound : ∀ z, riemannianEDist I p z < 3 * (r : ℝ≥0∞) →
      ‖mfderiv I (𝓘(ℝ, F)) f z‖ₑ ≤ K)
    {x y : M} (hx : riemannianEDist I p x < r) (hy : riemannianEDist I p y < r) :
    edist (f x) (f y) ≤ (K : ℝ≥0∞) * riemannianEDist I x y := by
  have hxy : riemannianEDist I x y < 2 * (r : ℝ≥0∞) := by
    calc
      riemannianEDist I x y ≤ riemannianEDist I x p + riemannianEDist I p y :=
        riemannianEDist_triangle
      _ < (r : ℝ≥0∞) + r := ENNReal.add_lt_add (by rwa [riemannianEDist_comm]) hy
      _ = 2 * (r : ℝ≥0∞) := (two_mul _).symm
  have hdiv : edist (f x) (f y) / (K : ℝ≥0∞) ≤ riemannianEDist I x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
      exists_lt_of_riemannianEDist_lt (lt_min hb hxy)
    have hγball : ∀ t ∈ Icc (0 : ℝ) 1,
        riemannianEDist I p (γ t) < 3 * (r : ℝ≥0∞) := by
      intro t ht
      have hxt : riemannianEDist I x (γ t) < 2 * (r : ℝ≥0∞) :=
        ((riemannianEDist_le_pathELength
          (hγsmooth.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1).trans
          (pathELength_mono le_rfl ht.2)).trans_lt
          (hγlength.trans_le (min_le_right _ _))
      calc
        riemannianEDist I p (γ t) ≤ riemannianEDist I p x + riemannianEDist I x (γ t) :=
          riemannianEDist_triangle
        _ < (r : ℝ≥0∞) + 2 * r := ENNReal.add_lt_add hx hxt
        _ = 3 * (r : ℝ≥0∞) := by ring
    have hdist := edist_le_mul_pathELength_of_mfderiv_le hf hbound hγsmooth hγball
    rw [hγ0, hγ1] at hdist
    apply (ENNReal.div_le_iff (by exact_mod_cast hK.ne') ENNReal.coe_ne_top).mpr
    calc
      edist (f x) (f y) ≤ (K : ℝ≥0∞) * pathELength I γ 0 1 := hdist
      _ ≤ b * K := by
        rw [mul_comm b]
        exact mul_le_mul_right (hγlength.le.trans (min_le_left _ _)) _
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (by exact_mod_cast hK.ne') ENNReal.coe_ne_top).mp hdiv

variable [IsManifold I 1 M] [RegularSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

set_option backward.isDefEq.respectTransparency false in


theorem exists_nhds_edist_le_mul_riemannianEDist_of_mfderiv_le
    {f : M → F} {s : Set M} {p : M} (hs : s ∈ 𝓝 p)
    (hf : ∀ z ∈ s, ContMDiffAt I (𝓘(ℝ, F)) 1 f z)
    {K : ℝ≥0} (hK : 0 < K)
    (hbound : ∀ z ∈ s, ‖mfderiv I (𝓘(ℝ, F)) f z‖ₑ ≤ K) :
    ∃ v ∈ 𝓝 p, v ⊆ s ∧ ∀ x ∈ v, ∀ y ∈ v,
      edist (f x) (f y) ≤ (K : ℝ≥0∞) * riemannianEDist I x y := by
  obtain ⟨c, hc, hcs⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hs
  let r : ℝ≥0 := c / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have h3r : 3 * (r : ℝ≥0∞) = c := by
    exact_mod_cast (show (3 : ℝ≥0) * (c / 3) = c by
      rw [mul_div_cancel₀ _ (by norm_num)])
  have hball : {z | riemannianEDist I p z < 3 * (r : ℝ≥0∞)} ⊆ s := by
    simpa only [h3r] using hcs
  refine ⟨{z | riemannianEDist I p z < r},
    eventually_riemannianEDist_lt I p (by exact_mod_cast hr), ?_, ?_⟩
  · intro z hz
    apply hball
    change riemannianEDist I p z < (r : ℝ≥0∞) at hz
    exact hz.trans_le (by nth_rw 1 [← one_mul (r : ℝ≥0∞)]; gcongr; norm_num)
  · intro x hx y hy
    exact edist_le_mul_riemannianEDist_of_mfderiv_le_on_ball hK
      (fun z hz ↦ hf z (hball hz)) (fun z hz ↦ hbound z (hball hz)) hx hy

end Poincare
