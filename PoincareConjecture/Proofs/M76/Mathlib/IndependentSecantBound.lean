import PoincareConjecture.Proofs.M76.Mathlib.UniformSecantProjection










set_option autoImplicit false

open Set

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem LinearIndependent.exists_pos_secant_bound_of_injOn {v : ι → E}
    (hv : LinearIndependent ℝ v) (faces : Set (Finset ι)) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι)))),
      ∀ y ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι)))),
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  let V := Submodule.span ℝ (range v)
  let b : Module.Basis ι ℝ V := Module.Basis.span hv
  let S : Set V := ⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι)))
  have hb : (fun i => V.subtype (b i)) = v :=
    funext (fun i => Module.Basis.coe_span_apply hv i)
  have himage : V.subtype '' S =
      ⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι))) := by
    simp only [S, image_iUnion, V.subtype.image_convexHull, image_insert_eq,
      map_zero, image_image, hb]
  have hQV : InjOn (Q.comp V.subtypeL) S := by
    intro x hx y hy he
    apply Subtype.ext
    apply hQ
    · rw [← himage]
      exact mem_image_of_mem _ hx
    · rw [← himage]
      exact mem_image_of_mem _ hy
    · exact he
  obtain ⟨c, hc, hbound⟩ := b.exists_pos_secant_bound_of_injOn faces (Q.comp V.subtypeL) hQV
  refine ⟨c, hc, ?_⟩
  rw [← himage]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hbound x hx y hy

namespace AbstractSimplicialComplex




theorem RadialEmbedding.exists_pos_secant_bound_of_linearIndependent
    {A : AbstractSimplicialComplex ι} (v : A.RadialEmbedding E)
    (hv : LinearIndependent ℝ v.val) (Q : E →L[ℝ] F) (hQ : InjOn Q v.cone.space) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ v.cone.space, ∀ y ∈ v.cone.space,
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  rw [RadialEmbedding.cone_space] at hQ ⊢
  exact hv.exists_pos_secant_bound_of_injOn (insert ∅ A.faces) Q hQ

end AbstractSimplicialComplex
