import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeLinkInterval
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualLink
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]





theorem isFinitePLBallPair_dualLink_of_interval
    {s : Finset E} (hs : s ∈ K.faces)
    (a b : (K.faceLink s).vertices)
    (hI : IsFinitePLBallPair ℝ (K.faceLink s).space {(a : E), (b : E)}) :
    IsFinitePLBallPair ℝ ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space
      {(s ∪ {(a : E)}).centroid ℝ id, (s ∪ {(b : E)}).centroid ℝ id} := by
  obtain ⟨f, e, he, hvertex, hvalue⟩ := K.exists_finitePL_barycentricDualLink hs
  obtain ⟨g, hg, hge⟩ := he
  have hf : FinitePiecewiseAffineOn f (K.faceLink s).space := by
    apply hg.congr
    intro x hx
    exact (hge ⟨x, hx⟩).symm.trans (hvalue ⟨x, hx⟩)
  have hi : InjOn f (K.faceLink s).space := by
    intro x hx y hy hxy
    apply congrArg Subtype.val (e.injective (show e ⟨x, hx⟩ = e ⟨y, hy⟩ from ?_))
    apply Subtype.ext
    exact (hvalue ⟨x, hx⟩).trans (hxy.trans (hvalue ⟨y, hy⟩).symm)
  have himage : f '' (K.faceLink s).space =
      ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hvalue ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).property
    · intro y hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      exact (hvalue _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))
  have ha : f a = (s ∪ {(a : E)}).centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using hvertex {(a : E)} a.property
  have hb : f b = (s ∪ {(b : E)}).centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using hvertex {(b : E)} b.property
  simpa only [himage, image_pair, ha, hb] using hI.image hf hi

end Geometry.SimplicialComplex
