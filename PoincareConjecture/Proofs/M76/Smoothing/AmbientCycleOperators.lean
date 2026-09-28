import PoincareConjecture.Proofs.M76.Mathlib.OrthogonalOperatorSplit
import PoincareConjecture.Proofs.M76.Smoothing.CycleFrameCoordinates











set_option autoImplicit false

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



abbrev CycleFrameRadialOperatorSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (cycleFrameInclusion b) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}




noncomputable def cycleFrameRadialOperatorHomeomorph (n : ℕ)
    (b : Module.Basis (Fin (n + 3)) ℝ E) :
    CycleFrameRadialOperatorSpace n b ≃ₜ CycleProjectionSpace n b (Real.pi / 2) := by
  let e : CycleFrameRadialOperatorSpace n b ≃ₜ
      {Q : (cycleFrameInclusion b).FrameProjectionSpace //
        (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q.val (b i))} :=
    { toFun := fun Q => ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
      invFun := fun Q => ⟨Q.val.val, Q.val.property, Q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun _ => _) }
  exact e.trans (cycleFrameProjectionHomeomorph n b)



abbrev AmbientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (V.subtypeL.comp (cycleFrameInclusion b)) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}




noncomputable def ambientCycleProjectionHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    AmbientCycleProjectionSpace n V b ≃ₜ
      (CycleProjectionSpace n b (Real.pi / 2) × (Vᗮ →L[ℝ] ℂ)) :=
  (V.operatorRestrictionHomeomorph (fun R : V →L[ℝ] ℂ =>
    Function.RightInverse (cycleFrameInclusion b) R ∧
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => R (b i)))).trans
        ((cycleFrameRadialOperatorHomeomorph n b).prodCongr (Homeomorph.refl _))




theorem contractible_ambientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (AmbientCycleProjectionSpace n V b) := by
  let := contractible_cycleProjectionSpace n b
    (show Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi from
      ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩)
  exact (ambientCycleProjectionHomeomorph n V b).contractibleSpace




noncomputable def ambientFrameCycleHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    {Q : (V.subtypeL.comp (cycleFrameInclusion b)).FrameProjectionSpace //
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q.val (b i))} ≃ₜ
      AmbientCycleProjectionSpace n V b where
  toFun Q := ⟨Q.val.val, Q.val.property, Q.property⟩
  invFun Q := ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun _ => _)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)

end PoincareConjecture.M76.Smoothing
