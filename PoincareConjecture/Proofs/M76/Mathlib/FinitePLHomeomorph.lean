import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s : Set E} {t : Set F} {u : Set G}





def IsFinitePL (e : s ≃ₜ t) : Prop :=
  ∃ f : E → F, FinitePiecewiseAffineOn f s ∧ ∀ x : s, (e x : F) = f x



theorem IsFinitePL.symm [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {e : s ≃ₜ t} (he : e.IsFinitePL) : e.symm.IsFinitePL := by
  classical
  obtain ⟨f, hf, he⟩ := he
  let g : F → E := fun y => if hy : y ∈ t then e.symm ⟨y, hy⟩ else 0
  have hg (y : t) : g y = (e.symm y : E) := by simp [g, y.property]
  have hleft : LeftInvOn g f s := by
    intro x hx
    rw [← he ⟨x, hx⟩, hg, e.symm_apply_apply]
  have himage : f '' s = t := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← he ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← he, e.apply_symm_apply]
  refine ⟨g, ?_, fun y => (hg y).symm⟩
  rw [← himage]
  exact hf.inverse hleft




theorem IsFinitePL.trans [FiniteDimensional ℝ F]
    {e : s ≃ₜ t} {d : t ≃ₜ u} (he : e.IsFinitePL) (hd : d.IsFinitePL) :
    (e.trans d).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  obtain ⟨g, hg, hd⟩ := hd
  have hmap : MapsTo f s t := by
    intro x hx
    rw [← he ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  refine ⟨g ∘ f, hg.comp hf hmap, ?_⟩
  intro x
  change (d (e x) : G) = g (f x)
  rw [hd, he]



theorem isFinitePL_setCongr {s t : Set E} (h : s = t)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hs : K.space = s) :
    (Homeomorph.setCongr h).IsFinitePL := by
  refine ⟨id, ⟨K, hK, hs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩, ?_⟩
  exact fun _ => rfl

end Homeomorph
