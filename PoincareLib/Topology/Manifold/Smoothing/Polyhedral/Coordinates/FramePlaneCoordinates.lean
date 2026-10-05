import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.LeafFields.BasisTransversePlanes

/-!
# Coordinates in an arbitrary independent frame

The normalized kernel correspondence can use an arbitrary injective
frame with its own coordinate type, rather than the subtype of its
image. Only a continuous linear change of target coordinates is used.
See Cairns 1940, Lemma 5.1, p. 801, and M76 derivation 30.
-/

set_option autoImplicit false

namespace ContinuousLinearMap

/-- Projection operators fixing a given coordinate frame.
See Cairns p. 801 and M76 derivation 30. -/
abbrev FrameProjectionSpace {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J : F →L[ℝ] E) :=
  {Q : E →L[ℝ] F // Function.RightInverse J Q}

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Changing the target from frame coordinates to the actual frame
subspace identifies normalized operators with retractions.
See Cairns p. 801 and M76 derivation 30. -/
noncomputable def frameRetractionHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J) :
    J.FrameProjectionSpace ≃ₜ J.range.RetractionSpace := by
  let e := (LinearEquiv.ofInjective J.toLinearMap hJ).toContinuousLinearEquiv
  refine ((ContinuousLinearEquiv.refl ℝ E).arrowCongr e).toHomeomorph.subtype ?_
  intro Q
  change Function.RightInverse J Q ↔ ∀ u : J.range, e (Q u) = u
  constructor
  · intro h u
    obtain ⟨u, z, rfl⟩ := u
    change e (Q (J z)) = e z
    rw [h z]
  · intro h z
    apply e.injective
    exact h (e z)

omit [FiniteDimensional ℝ E] in
/-- Target-coordinate conversion preserves the geometric kernel.
See Cairns p. 801 and M76 derivation 30. -/
theorem ker_frameRetractionHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (Q : J.FrameProjectionSpace) :
    ((J.frameRetractionHomeomorph hJ) Q).val.ker = Q.val.ker := by
  let e := (LinearEquiv.ofInjective J.toLinearMap hJ).toContinuousLinearEquiv
  ext x
  change e (Q.val x) = 0 ↔ Q.val x = 0
  exact e.map_eq_zero_iff

/-- Complementary geometric planes correspond to projections fixing
any independent coordinate frame.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def frameComplementPlaneHomeomorph (J : F →L[ℝ] E)
    (hJ : Function.Injective J) :
    J.range.ComplementPlaneSpace ≃ₜ J.FrameProjectionSpace :=
  J.range.complementPlaneHomeomorph.trans (J.frameRetractionHomeomorph hJ).symm

/-- The frame-normalized projection has exactly its original plane
as kernel. See Cairns p. 801 and M76 derivation 30. -/
theorem ker_frameComplementPlaneHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (K : J.range.ComplementPlaneSpace) :
    ((J.frameComplementPlaneHomeomorph hJ) K).val.ker = K.val.subspace := by
  rw [← J.ker_frameRetractionHomeomorph hJ]
  have he : (J.frameRetractionHomeomorph hJ) ((J.frameComplementPlaneHomeomorph hJ) K) =
      J.range.complementRetraction K :=
    (J.frameRetractionHomeomorph hJ).apply_symm_apply _
  rw [he]
  exact J.range.ker_complementRetraction K

end ContinuousLinearMap

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The geometric transverse-plane correspondence in independent
frame coordinates, with exact radial realization as its range.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def frameBasisPlaneHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (J : F →L[ℝ] E) (hJ : Function.Injective J) :
    J.range.TransverseComplementPlaneSpace (A.basisRadialEmbedding b).cone.space ≃ₜ
      {Q : J.FrameProjectionSpace // A.IsRadialEmbedding (fun i => Q.val (b i))} :=
  (J.frameComplementPlaneHomeomorph hJ).subtype (fun K => by
    rw [A.isRadialEmbedding_iff_isSecantTransverse_ker,
      J.ker_frameComplementPlaneHomeomorph hJ])

end AbstractSimplicialComplex
