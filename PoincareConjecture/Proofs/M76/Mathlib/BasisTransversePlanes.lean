import PoincareConjecture.Proofs.M76.Mathlib.BasisProjectionConverse
import PoincareConjecture.Proofs.M76.Mathlib.ComplementPlaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.SecantTransversality

set_option autoImplicit false

open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev TransverseComplementPlaneSpace (U : Submodule ℝ E) (S : Set E) :=
  {K : U.ComplementPlaneSpace // K.val.subspace.IsSecantTransverse S}

noncomputable def transversePlaneRetractionHomeomorph (U : Submodule ℝ E) (S : Set E) :
    U.TransverseComplementPlaneSpace S ≃ₜ
      {Q : U.RetractionSpace // Q.val.ker.IsSecantTransverse S} :=
  U.complementPlaneHomeomorph.subtype (fun K => by
    change K.val.subspace.IsSecantTransverse S ↔
      (U.complementRetraction K).val.ker.IsSecantTransverse S
    rw [U.ker_complementRetraction K])

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isRadialEmbedding_iff_isSecantTransverse_ker (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      Q.ker.IsSecantTransverse (A.basisRadialEmbedding b).cone.space := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ :=
      BasisRadialProjection.exists_pos_secant_bound (⟨Q, h⟩ : A.BasisRadialProjection b F)
    exact Submodule.isSecantTransverse_ker_of_lower_bound Q hc hb
  · intro h
    exact A.isRadialEmbedding_of_injOn_basisCone b Q (h.injOn Q rfl)

noncomputable def basisTransversePlaneHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (U : Submodule ℝ E) :
    U.TransverseComplementPlaneSpace (A.basisRadialEmbedding b).cone.space ≃ₜ
      {Q : U.RetractionSpace // A.IsRadialEmbedding (fun i => Q.val (b i))} :=
  (U.transversePlaneRetractionHomeomorph (A.basisRadialEmbedding b).cone.space).trans
    (Homeomorph.setCongr (by
      ext Q
      exact (A.isRadialEmbedding_iff_isSecantTransverse_ker b Q.val).symm))

end AbstractSimplicialComplex
