import PoincareConjecture.Proofs.M76.Mathlib.BasisTransversePlanes
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas











set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




abbrev SecantTransversePlaneSpace (d : ℕ) (S : Set E) :=
  {K : EuclideanSubspace E // Module.finrank ℝ K.subspace + d = Module.finrank ℝ E ∧
    K.subspace.IsSecantTransverse S}




noncomputable def transverseComplementHomeomorph (d : ℕ) (S : Set E)
    (U : Submodule ℝ E) (hU : Module.finrank ℝ U = d)
    (hdisjoint : ∀ K : Submodule ℝ E, K.IsSecantTransverse S → Disjoint U K) :
    SecantTransversePlaneSpace d S ≃ₜ U.TransverseComplementPlaneSpace S where
  toFun K := ⟨⟨K.val, (Submodule.isCompl_iff_disjoint U K.val.subspace (by
    have hdim := K.property.1
    omega)).mpr (hdisjoint _ K.property.2)⟩, K.property.2⟩
  invFun K := ⟨K.val.val, ⟨by
    have hdim := Submodule.finrank_add_eq_of_isCompl K.val.property
    omega, K.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun _ => _)

end Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]




theorem disjoint_faceSpan_of_isSecantTransverse (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) {s : Finset ι} (hs : s ∈ A.faces)
    {K : Submodule ℝ E} (hK : K.IsSecantTransverse (A.basisRadialEmbedding b).cone.space) :
    Disjoint (Submodule.span ℝ (b '' (s : Set ι))) K := by
  let R := ContinuousLinearMap.id ℝ E - K.starProjection
  have hker : R.ker = K := by
    ext x
    change (x - K.starProjection x = 0) ↔ x ∈ K
    rw [sub_eq_zero, eq_comm, K.starProjection_eq_self_iff]
  have hsimplex : convexHull ℝ (insert 0 (b '' (s : Set ι))) ⊆
      (A.basisRadialEmbedding b).cone.space := by
    rw [RadialEmbedding.cone_space]
    exact subset_iUnion₂_of_subset s (mem_insert_of_mem _ hs) Subset.rfl
  have hinj := b.injOn_span_of_injOn_simplex R ((hK.injOn R hker).mono hsimplex)
  apply Submodule.disjoint_def.mpr
  intro x hx hk
  apply hinj hx (Submodule.zero_mem _)
  change x - K.starProjection x = 0 - K.starProjection 0
  rw [K.starProjection_eq_self_iff.mpr hk, map_zero, sub_self, sub_self]

end AbstractSimplicialComplex
