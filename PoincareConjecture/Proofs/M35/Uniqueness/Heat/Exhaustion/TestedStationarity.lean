import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.CompactTestTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem vector_heat_test_hasDerivAt
    {a b t : ℝ} (ht : t ∈ Ioo a b) {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (X : ℝ → V → V)
    (hX : ContDiffOn ℝ ∞ (Function.uncurry X) (Ioo a b ×ˢ univ))
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (k : Fin n)
    (hheat : ∀ x ∈ tsupport φ, HasDerivAt (fun s => X s x)
      (@Add.add V inferInstance
        (∑ i, fieldHessian D (X t) x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
        (RicciFlow.ricciSharp D x (X t x))) t) :
    HasDerivAt (fun s => ∫ x, φ x * X s x k)
      (∫ x, φ x * (@Add.add V inferInstance
        (∑ i, fieldHessian D (X t) x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
        (RicciFlow.ricciSharp D x (X t x))) k) t := by
  have hcomponent : ContDiffOn ℝ ∞ (fun p : ℝ × V => X p.1 p.2 k) (Ioo a b ×ˢ univ) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn hX
  apply (compact_test_time_hasDerivAt ht hcomponent hφ hc).congr_deriv
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ tsupport φ
  · have hd := ((hcomponent (t, x) ⟨ht, mem_univ x⟩).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
        ).differentiableAt (by simp)
    have hdt := hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    have he := hdt.unique ((EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp_hasDerivAt t
      (hheat x hx))
    exact congrArg (fun z : ℝ => φ x * z) he
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem exists_raw_tested_stationarity_bound
    {J : Set ℝ} (F : RicciFlow n V J) {T : ℝ} (hT : 0 ≤ T) (hTJ : Icc 0 T ⊆ J)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ → V → V,
      (∀ t, ContDiff ℝ ∞ (X t)) →
      ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ univ) →
      ContDiffOn ℝ ∞ (Function.uncurry X) (Ioo 0 T ×ˢ univ) →
      (∀ t ∈ Ioo 0 T, ∀ x ∈ tsupport φ, HasDerivAt (fun s => X s x)
        (@Add.add V inferInstance
          (∑ i, fieldHessian (F.connection t) (X t) x
            ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x i))
          (RicciFlow.ricciSharp (F.connection t) x (X t x))) t) →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ t ∈ Icc 0 T, ∀ x ∈ tsupport φ,
        ((F.metric t).tensorNorm (killingDefectTensor (F.connection t) (X t)) x) ^ 2 ≤ δ ^ 2) →
      ∀ t ∈ Icc 0 T,
        |(∫ x, φ x * X t x k) - (∫ x, φ x * X 0 x k)| ≤ C * δ := by
  obtain ⟨C, hC, hb⟩ := exists_raw_vector_heat_test_bound F isCompact_Icc hTJ hφ hc k
  refine ⟨C * T, mul_nonneg hC hT, ?_⟩
  intro X hXs hXc hX hheat δ hδ hdefect t ht
  let f := fun s => ∫ x, φ x * X s x k
  let d := fun s => ∫ x, φ x * (@Add.add V inferInstance
    (∑ i, fieldHessian (F.connection s) (X s) x
      ((F.metric s).orthonormalBasis x i) ((F.metric s).orthonormalBasis x i))
    (RicciFlow.ricciSharp (F.connection s) x (X s x))) k
  have hfc : ContinuousOn f (Icc 0 T) :=
    continuousOn_integral_of_compact_support hc
      ((hφ.continuous.comp continuous_snd).continuousOn.mul
        ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn hXc))
      (fun _ _ _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
  have htd : ∀ s ∈ Ioo 0 T, HasDerivAt f (d s) s := fun s hs =>
    vector_heat_test_hasDerivAt hs (F.connection s) X hX hφ.continuous hc k (hheat s hs)
  have hsmall : |f t - f 0| ≤ (C * δ) * t := by
    simpa only [sub_zero] using abs_sub_le_of_closed_interval_derivative_bound ht.1
      (hfc.mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => htd s ⟨hs.1, hs.2.trans_le ht.2⟩)
      (fun s hs => hb s ⟨hs.1.le, hs.2.le.trans ht.2⟩ (X s) (hXs s) δ hδ
        (hdefect s ⟨hs.1.le, hs.2.le.trans ht.2⟩))
  calc
    _ ≤ (C * δ) * t := hsmall
    _ ≤ (C * δ) * T := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hC hδ)
    _ = (C * T) * δ := by ring

end PoincareConjecture.M35.Uniqueness.Heat
