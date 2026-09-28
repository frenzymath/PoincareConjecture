import PoincareConjecture.Proofs.M76.Mathlib.FramePlaneCoordinates
import PoincareConjecture.Proofs.M76.Smoothing.CycleProjectionSpace

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def cycleFrameInclusion {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (b 0) + Complex.imCLM.smulRight (b 1)

theorem cycleFrameInclusion_one {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b 1 = b 0 := by simp [cycleFrameInclusion]

theorem cycleFrameInclusion_I {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b Complex.I = b 1 := by simp [cycleFrameInclusion]

theorem injective_cycleFrameInclusion {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    Function.Injective (cycleFrameInclusion b) := by
  have hne : (0 : Fin (n + 3)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one] at hv
    omega
  intro z w h
  apply Complex.ext
  · have he := congrArg (fun x => b.repr x 0) h
    simpa [cycleFrameInclusion, hne, Ne.symm hne] using he
  · have he := congrArg (fun x => b.repr x 1) h
    simpa [cycleFrameInclusion, hne, Ne.symm hne] using he

theorem rightInverse_cycleFrameInclusion_iff {n : ℕ}
    (b : Module.Basis (Fin (n + 3)) ℝ E) (Q : E →L[ℝ] ℂ) :
    Function.RightInverse (cycleFrameInclusion b) Q ↔ Q (b 0) = 1 ∧ Q (b 1) = Complex.I := by
  constructor
  · intro h
    exact ⟨by simpa only [cycleFrameInclusion_one] using h 1,
      by simpa only [cycleFrameInclusion_I] using h Complex.I⟩
  · rintro ⟨hzero, hone⟩ z
    change Q (z.re • b 0 + z.im • b 1) = z
    rw [map_add, map_smul, map_smul, hzero, hone, Complex.real_smul, Complex.real_smul,
      mul_one, Complex.re_add_im]

theorem rightInverse_cycleFrameInclusion_iff_fixed {n : ℕ}
    (b : Module.Basis (Fin (n + 3)) ℝ E)
    (Q : (cyclicEdgeComplex n).BasisRadialProjection b ℂ) :
    Function.RightInverse (cycleFrameInclusion b) Q.val ↔
      EqOn (fun i => Q.val (b i)) (cycleFrame n (Real.pi / 2)) ({0, 1} : Set (Fin (n + 3))) := by
  rw [rightInverse_cycleFrameInclusion_iff]
  have he : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
    rw [Circle.coe_exp]
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using Complex.exp_pi_div_two_mul_I
  simpa only [he] using (fixedCycleVertexValues_iff (theta := Real.pi / 2)
    (⟨fun i => Q.val (b i), Q.property⟩ : (cyclicEdgeComplex n).RadialEmbedding ℂ)).symm

noncomputable def cycleFrameProjectionHomeomorph (n : ℕ)
    (b : Module.Basis (Fin (n + 3)) ℝ E) :
    {Q : (cycleFrameInclusion b).FrameProjectionSpace //
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q.val (b i))} ≃ₜ
      CycleProjectionSpace n b (Real.pi / 2) where
  toFun Q := ⟨⟨Q.val.val, Q.property⟩,
    (rightInverse_cycleFrameInclusion_iff_fixed b ⟨Q.val.val, Q.property⟩).mp Q.val.property⟩
  invFun Q := ⟨⟨Q.val.val, (rightInverse_cycleFrameInclusion_iff_fixed b Q.val).mpr Q.property⟩,
    Q.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun _ => _) |>.subtype_mk (fun _ => _)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun _ => _) |>.subtype_mk (fun _ => _)

end PoincareConjecture.M76.Smoothing
