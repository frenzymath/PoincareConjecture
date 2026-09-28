import PoincareConjecture.Proofs.M76.Mathlib.AffineSubdivisionComposition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement










set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]




def FinitePiecewiseAffineOn (f : E → F) (s : Set E) : Prop :=
  ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = s ∧ K.AffineOnFaces f

variable {f f' : E → F} {g : F → G} {s : Set E} {t : Set F}



theorem SimplicialComplex.AffineOnFaces.finitePiecewiseAffineOn
    {K : SimplicialComplex ℝ E} (hf : K.AffineOnFaces f) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn f K.space := ⟨K, hK, rfl, hf⟩



theorem FinitePiecewiseAffineOn.congr (hf : FinitePiecewiseAffineOn f s)
    (heq : EqOn f f' s) : FinitePiecewiseAffineOn f' s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨K, hK, rfl, hfaces.congr heq⟩



theorem FinitePiecewiseAffineOn.isCompact (hf : FinitePiecewiseAffineOn f s) :
    IsCompact s := by
  obtain ⟨K, hK, rfl, _⟩ := hf
  exact K.isCompact_space_of_finite hK



theorem FinitePiecewiseAffineOn.continuousOn (hf : FinitePiecewiseAffineOn f s) :
    ContinuousOn f s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact hfaces.continuousOn hK



theorem FinitePiecewiseAffineOn.comp [FiniteDimensional ℝ F]
    (hg : FinitePiecewiseAffineOn g t) (hf : FinitePiecewiseAffineOn f s)
    (hmap : MapsTo f s t) : FinitePiecewiseAffineOn (g ∘ f) s := by
  classical
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  obtain ⟨L, hL, rfl, hgfaces⟩ := hg
  let N := hK.toFinset.sup Finset.card
  have hN (r : Finset E) (hr : r ∈ K.faces) : r.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hr)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRK, _, hcomp⟩ :=
    hfaces.exists_subdivision_comp hgfaces hK hL hmap hN
  exact ⟨R, hR, hRK.space_eq, hcomp⟩




theorem FinitePiecewiseAffineOn.restrict [FiniteDimensional ℝ E]
    (hf : FinitePiecewiseAffineOn f s) (J : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hJs : J.space ⊆ s) :
    FinitePiecewiseAffineOn f J.space := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  obtain ⟨R, hR, hRJ, href⟩ :=
    J.exists_finite_refinement_of_space_subset K hJ hK hJs
  exact ⟨R, hR, hRJ.space_eq, hfaces.of_face_containment href⟩




theorem FinitePiecewiseAffineOn.inverse [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (hf : FinitePiecewiseAffineOn f s)
    {g : F → E} (hleft : LeftInvOn g f s) :
    FinitePiecewiseAffineOn g (f '' s) := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨hfaces.embeddedImage hleft.injOn,
    hfaces.embeddedImage_finite _ hK, hfaces.embeddedImage_space _,
    hfaces.inverse_on_embeddedImage hleft.injOn hleft⟩

end Geometry
