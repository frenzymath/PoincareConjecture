import PoincareConjecture.Proofs.M76.Mathlib.ConicalAffineExtension

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {f : E → F}

theorem AffineOnFaces.exists_height_preserving_cone_extension
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) (hK : K.faces.Finite)
    (hlinK : ∀ r ∈ K.faces, LinearIndependent ℝ ((↑) : r → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ r ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : r → F))
    (hradL : InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space)
    (A : E →ₗ[ℝ] ℝ) (B : F →ₗ[ℝ] ℝ)
    (hheight : ∀ x ∈ K.space, B (f x) = A x) :
    ∃ e : (K.coneAtZero hlinK hradK).space ≃ₜ
        ((hf.embeddedImage hinj).coneAtZero hlinL hradL).space,
      e.IsFinitePL ∧ (∀ x, B (e x) = A x) ∧
        ∀ x : K.space,
          (e ⟨x, space_subset_of_le (le_coneAtZero hlinK hradK) x.property⟩ : F) = f x := by
  obtain ⟨g, e, hg, hg0, hbase, he⟩ :=
    hf.exists_cone_extension_affine hinj hK hlinK hradK hlinL hradL
  let Ac : E →ᴬ[ℝ] ℝ := A.toContinuousLinearMap.toContinuousAffineMap
  let Bc : F →ᴬ[ℝ] ℝ := B.toContinuousLinearMap.toContinuousAffineMap
  have hAg : EqOn (B ∘ g) A (K.coneAtZero hlinK hradK).space := by
    apply (hg.postcomp Bc).eqOn_of_eqOn_vertices
      ((K.coneAtZero hlinK hradK).affineOnFaces_affine Ac)
    intro x hx
    rw [coneAtZero_vertices] at hx
    rcases hx with rfl | hx
    · change B (g 0) = A 0
      rw [hg0, map_zero, map_zero]
    · change B (g x) = A x
      rw [hbase (K.vertices_subset_space hx)]
      exact hheight x (K.vertices_subset_space hx)
  refine ⟨e, ⟨g, hg.finitePiecewiseAffineOn (finite_coneAtZero_faces hK hlinK hradK), he⟩,
    ?_, ?_⟩
  · intro x
    rw [he]
    exact hAg x.property
  · intro x
    exact (he ⟨x, space_subset_of_le (le_coneAtZero hlinK hradK) x.property⟩).trans
      (hbase x.property)

end Geometry.SimplicialComplex
