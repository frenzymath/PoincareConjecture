import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_independent_basis_realization (K : SimplicialComplex ℝ E)
    (b : Module.Basis K.vertices ℝ F) :
    ∃ (f : E → F) (hf : K.AffineOnFaces f) (hinj : InjOn f K.space),
      AffineIndependent ℝ ((↑) : (hf.embeddedImage hinj).vertices → F) ∧
      LeftInvOn (b.constr ℝ ((↑) : K.vertices → E)) f K.space ∧
      ∀ v : K.vertices, f v = b v := by
  classical
  let v : E → F := Function.extend ((↑) : K.vertices → E) b (fun _ => 0)
  have hv (x : K.vertices) : v x = b x := Subtype.val_injective.extend_apply b (fun _ => 0) x
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices v
  let Q := b.constr ℝ ((↑) : K.vertices → E)
  let a : F →ᴬ[ℝ] E := ⟨Q.toAffineMap, Q.continuous_of_finiteDimensional⟩
  have hleft : LeftInvOn Q f K.space :=
    (hf.postcomp a).eqOn_of_eqOn_vertices
      (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)) (by
        intro x hx
        change Q (f x) = x
        rw [hfv hx, hv ⟨x, hx⟩]
        exact b.constr_basis ℝ ((↑) : K.vertices → E) ⟨x, hx⟩)
  have hinj : InjOn f K.space := hleft.injOn
  have hfb (x : K.vertices) : f x = b x := (hfv x.property).trans (hv x)
  have hr : f '' K.vertices = range b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hfb ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, hfb x⟩
  refine ⟨f, hf, hinj, ?_, hleft, hfb⟩
  rw [hf.embeddedImage_vertices hinj, hr]
  exact b.linearIndependent.affineIndependent.range

theorem exists_independent_euclidean_realization (K : SimplicialComplex ℝ E)
    [Fintype K.vertices] :
    ∃ (f : E → EuclideanSpace ℝ K.vertices) (hf : K.AffineOnFaces f)
      (hinj : InjOn f K.space),
      AffineIndependent ℝ ((↑) : (hf.embeddedImage hinj).vertices → EuclideanSpace ℝ K.vertices) ∧
      ∀ v : K.vertices, f v = EuclideanSpace.basisFun K.vertices ℝ v := by
  obtain ⟨f, hf, hinj, hvertices, _, hfb⟩ :=
    K.exists_independent_basis_realization (EuclideanSpace.basisFun K.vertices ℝ).toBasis
  exact ⟨f, hf, hinj, hvertices, hfb⟩

end Geometry.SimplicialComplex
