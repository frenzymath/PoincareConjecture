import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FramePlaneCoordinates
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.CycleProjectionSpace

/-!
# A fixed coordinate frame in a cyclic basis star

The first two source basis vectors provide a real-linear complex frame.
Fixing that frame is exactly the previously used cycle normalization
at angle pi/2. See Cairns 1940, p. 801 and p. 807, footnote 14,
and M76 derivation 31.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complex coordinate plane spanned by the first cyclic edge.
See Cairns p. 801 and M76 derivation 31. -/
noncomputable def cycleFrameInclusion {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (b 0) + Complex.imCLM.smulRight (b 1)

/-- The real unit maps to the first source vertex.
See Cairns p. 801 and M76 derivation 31. -/
theorem cycleFrameInclusion_one {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b 1 = b 0 := by simp [cycleFrameInclusion]

/-- The imaginary unit maps to the second source vertex.
See Cairns p. 801 and M76 derivation 31. -/
theorem cycleFrameInclusion_I {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b Complex.I = b 1 := by simp [cycleFrameInclusion]

/-- The two distinct basis coefficients make this frame injective.
See Cairns p. 801 and M76 derivation 31. -/
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

/-- Fixing the complex frame means fixing its two basis vectors.
See Cairns p. 801 and M76 derivation 31. -/
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

/-- At angle pi/2 the fixed-edge conditions are exactly the right
inverse condition for the source frame.
See Cairns pp. 801, 807 and M76 derivation 31. -/
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

/-- The normalized frame operators and the fixed-edge projection
space are homeomorphic, retaining their operator coordinates.
See Cairns pp. 801, 807 and M76 derivation 31. -/
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

end PoincareMT.M76.Smoothing
