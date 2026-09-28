import PoincareConjecture.Proofs.M76.Mathlib.RadialRescaling
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHomeomorph










set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E}




theorem injOn_pos_smul_vertices
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    InjOn (fun x => r x • x) K.vertices := by
  intro x hx y hy hxy
  apply hinj (vertices_subset_space hx) (vertices_subset_space hy)
  have h := congrArg NormedSpace.normalize hxy
  simpa only [normalize_smul_of_pos (hr x hx), normalize_smul_of_pos (hr y hy)] using h

variable [DecidableEq E]



theorem radialRescale_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    (K.radialRescale hlin hinj r hr).vertices = (fun x => r x • x) '' K.vertices := by
  ext y
  constructor
  · intro hy
    obtain ⟨s, hs, he⟩ := hy
    change s.image (fun x => r x • x) = {y} at he
    have hyimage : y ∈ s.image (fun x => r x • x) := by rw [he]; simp
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyimage
    exact ⟨x, face_subset_vertices hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨{x}, hx, by simp⟩

variable [FiniteDimensional ℝ E]




theorem exists_radialRescale_homeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    ∃ (f g : E → E) (e : K.space ≃ₜ (K.radialRescale hlin hinj r hr).space),
      K.AffineOnFaces f ∧ (K.radialRescale hlin hinj r hr).AffineOnFaces g ∧
      EqOn f (fun x => r x • x) K.vertices ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      (∀ y : (K.radialRescale hlin hinj r hr).space, (e.symm y : E) = g y) := by
  let v : E → E := fun x => r x • x
  let w : E → E := Function.invFunOn v K.vertices
  have hv := injOn_pos_smul_vertices hinj r hr
  obtain ⟨f, g, e, hf, hg, hfv, _, hef, heg⟩ :=
    K.exists_homeomorph_of_vertex_maps (K.radialRescale hlin hinj r hr) hK v w
      (fun s hs => ⟨s.image v, ⟨s, hs, rfl⟩, by simp⟩)
      (by
        rintro _ ⟨s, hs, rfl⟩
        refine ⟨s, hs, ?_⟩
        rw [Finset.coe_image]
        exact (hv.invFunOn_image (face_subset_vertices hs)).subset)
      hv.leftInvOn_invFunOn
      (by
        rw [radialRescale_vertices]
        exact (surjOn_image v K.vertices).rightInvOn_invFunOn)
  exact ⟨f, g, e, hf, hg, hfv, hef, heg⟩



theorem exists_link_radialRescale_homeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (r : E → ℝ)
    (hr : ∀ x ∈ (K.link 0).vertices, 0 < r x) :
    ∃ (f g : E → E)
      (e : (K.link 0).space ≃ₜ
        ((K.link 0).radialRescale (fun _ hs => linearIndependent_of_mem_link_zero hs)
          (injOn_normalize_link K) r hr).space),
      (K.link 0).AffineOnFaces f ∧
      ((K.link 0).radialRescale (fun _ hs => linearIndependent_of_mem_link_zero hs)
        (injOn_normalize_link K) r hr).AffineOnFaces g ∧
      EqOn f (fun x => r x • x) (K.link 0).vertices ∧
      (∀ x : (K.link 0).space, (e x : E) = f x) ∧
      (∀ y, (e.symm y : E) = g y) :=
  (K.link 0).exists_radialRescale_homeomorph (finite_link_faces hK 0)
    (fun _ hs => linearIndependent_of_mem_link_zero hs) (injOn_normalize_link K) r hr

end Geometry.SimplicialComplex
