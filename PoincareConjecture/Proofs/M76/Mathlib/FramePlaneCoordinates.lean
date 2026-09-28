import PoincareConjecture.Proofs.M76.Mathlib.BasisTransversePlanes

set_option autoImplicit false

namespace ContinuousLinearMap

abbrev FrameProjectionSpace {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J : F →L[ℝ] E) :=
  {Q : E →L[ℝ] F // Function.RightInverse J Q}

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

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

theorem ker_frameRetractionHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (Q : J.FrameProjectionSpace) :
    ((J.frameRetractionHomeomorph hJ) Q).val.ker = Q.val.ker := by
  let e := (LinearEquiv.ofInjective J.toLinearMap hJ).toContinuousLinearEquiv
  ext x
  change e (Q.val x) = 0 ↔ Q.val x = 0
  exact e.map_eq_zero_iff

noncomputable def frameComplementPlaneHomeomorph (J : F →L[ℝ] E)
    (hJ : Function.Injective J) :
    J.range.ComplementPlaneSpace ≃ₜ J.FrameProjectionSpace :=
  J.range.complementPlaneHomeomorph.trans (J.frameRetractionHomeomorph hJ).symm

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

noncomputable def frameBasisPlaneHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (J : F →L[ℝ] E) (hJ : Function.Injective J) :
    J.range.TransverseComplementPlaneSpace (A.basisRadialEmbedding b).cone.space ≃ₜ
      {Q : J.FrameProjectionSpace // A.IsRadialEmbedding (fun i => Q.val (b i))} :=
  (J.frameComplementPlaneHomeomorph hJ).subtype (fun K => by
    rw [A.isRadialEmbedding_iff_isSecantTransverse_ker,
      J.ker_frameComplementPlaneHomeomorph hJ])

end AbstractSimplicialComplex
