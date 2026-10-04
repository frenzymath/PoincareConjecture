import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.OrthogonalOperatorSplit
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.CycleFrameCoordinates

/-!
# Cyclic projection coordinates in a larger ambient space

The source-subspace constraints fix a complex frame and a faithful
radial cycle. All operator coordinates on the orthogonal complement
are unrestricted. Thus the ambient operator space is a product with
a contractible vector space. See Cairns 1940, Lemma 5.2, p. 801,
and M76 derivation 32.
-/

set_option autoImplicit false

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Simultaneous frame and radial conditions expressed on a single
operator subtype. See Cairns p. 801 and M76 derivation 32. -/
abbrev CycleFrameRadialOperatorSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (cycleFrameInclusion b) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}

/-- Combining the frame and radial conditions does not change the
topology of the normalized cycle projection space.
See Cairns p. 801 and M76 derivation 32. -/
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

/-- Ambient operators whose restrictions realize the source cycle
with its first edge fixed. See Cairns p. 801 and M76 derivation 32. -/
abbrev AmbientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (V.subtypeL.comp (cycleFrameInclusion b)) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}

/-- Ambient cyclic operators split into the original constrained
projection space and arbitrary operators on the orthogonal complement.
See Cairns Lemma 5.2, p. 801, and M76 derivation 32. -/
noncomputable def ambientCycleProjectionHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    AmbientCycleProjectionSpace n V b ≃ₜ
      (CycleProjectionSpace n b (Real.pi / 2) × (Vᗮ →L[ℝ] ℂ)) :=
  (V.operatorRestrictionHomeomorph (fun R : V →L[ℝ] ℂ =>
    Function.RightInverse (cycleFrameInclusion b) R ∧
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => R (b i)))).trans
        ((cycleFrameRadialOperatorHomeomorph n b).prodCongr (Homeomorph.refl _))

/-- Enlarging the ambient space preserves contractibility of the
normalized cyclic operator space.
See Cairns Lemma 5.2, p. 801, and M76 derivation 32. -/
theorem contractible_ambientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (AmbientCycleProjectionSpace n V b) := by
  let := contractible_cycleProjectionSpace n b
    (show Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi from
      ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩)
  exact (ambientCycleProjectionHomeomorph n V b).contractibleSpace

/-- Flatten the two geometric frame-coordinate conditions without
altering the operator or its topology.
See Cairns p. 801 and M76 derivation 32. -/
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

end PoincareMT.M76.Smoothing
