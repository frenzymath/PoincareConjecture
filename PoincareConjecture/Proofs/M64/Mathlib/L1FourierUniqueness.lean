import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64L1Fourier_zero_continuous_pairing
    {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc 0 T))
    (hfourier : ∀ j : ℤ, (∫ x in Icc 0 T, fourier j (x : AddCircle T) * f x) = 0)
    (g : C(AddCircle T, ℂ)) :
    (∫ x in Icc 0 T, g (x : AddCircle T) * f x) = 0 := by
  let : Fact (0 < T) := ⟨hT⟩
  have hi (v : C(AddCircle T, ℂ)) :
      IntegrableOn (fun x : ℝ => v (x : AddCircle T) * f x) (Icc 0 T) :=
    hf.bdd_mul (v.continuous.comp (AddCircle.continuous_mk' T)).aestronglyMeasurable
      (Eventually.of_forall fun x => v.norm_coe_le_norm (x : AddCircle T))
  let L : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x in Icc 0 T, v (x : AddCircle T) * f x
      map_add' := fun v w => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hi v) (hi w)
      map_smul' := fun z v => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul z _ }
  have hbound (v : C(AddCircle T, ℂ)) :
      ‖L v‖ ≤ (∫ x in Icc 0 T, ‖f x‖) * ‖v‖ := by
    calc
      ‖L v‖ ≤ ∫ x in Icc 0 T, ‖v (x : AddCircle T) * f x‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in Icc 0 T, ‖v‖ * ‖f x‖ :=
        integral_mono (hi v).norm (hf.norm.const_mul _) fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (v.norm_coe_le_norm _) (norm_nonneg _)
      _ = (∫ x in Icc 0 T, ‖f x‖) * ‖v‖ := by rw [integral_const_mul, mul_comm]
  let A : C(AddCircle T, ℂ) →L[ℂ] ℂ := L.mkContinuous _ hbound
  have hspan : Submodule.span ℂ (range (@fourier T)) ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hfourier j
  have hfull := (Submodule.span ℂ (range (@fourier T))).topologicalClosure_minimal
    hspan A.isClosed_ker
  rw [span_fourier_closure_eq_top] at hfull
  exact hfull (Submodule.mem_top : g ∈ (⊤ : Submodule ℂ C(AddCircle T, ℂ)))

theorem m64L1Fourier_eq_zero
    {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc 0 T))
    (hfourier : ∀ j : ℤ, (∫ x in Icc 0 T, fourier j (x : AddCircle T) * f x) = 0) :
    f =ᵐ[volume.restrict (Icc 0 T)] (fun _ => 0) := by
  let : Fact (0 < T) := ⟨hT⟩
  have hzero : ∀ᵐ x ∂volume, x ∈ Ioo 0 T → f x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.mono_set Ioo_subset_Icc_self).locallyIntegrableOn
    intro phi hphi _ hsupp
    have hphi0 : phi 0 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => (hsupp h).1.false
    have hphiT : phi T = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => (hsupp h).2.false
    let g : C(AddCircle T, ℂ) :=
      ⟨AddCircle.liftIco T 0 (fun x => (phi x : ℂ)),
        AddCircle.liftIco_zero_continuous (by rw [hphi0, hphiT])
          (Complex.continuous_ofReal.comp hphi.continuous).continuousOn⟩
    have h := m64L1Fourier_zero_continuous_pairing hT hf hfourier g
    have heq : (∫ x in Icc 0 T, g (x : AddCircle T) * f x) =
        ∫ x in Icc 0 T, phi x • f x := by
      rw [← restrict_Ico_eq_restrict_Icc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      change AddCircle.liftIco T 0 (fun x => (phi x : ℂ)) (x : AddCircle T) * f x = _
      rw [AddCircle.liftIco_zero_coe_apply hx]
      exact Complex.real_smul.symm
    rw [heq] at h
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h
    · exact h
    · intro x hx
      have hp : phi x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hx (Ioo_subset_Icc_self (hsupp h))
      rw [hp, zero_smul]
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem measurableSet_Ioo] with x hx hm
  exact hx hm

end PoincareConjecture
