import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FullSubcomplexStars
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarPurity
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
theorem exists_planar_star_of_flat_ambient_star
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ N.vertices) → s ∈ N.faces)
    {p : E} (hp : p ∈ N.vertices) (f : E → V3)
    (hf : (K.closedStar p).AffineOnFaces f)
    (hfi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hzero : ∀ x ∈ (K.closedStar p).space, x ∈ N.space ↔ (f x) 0 = 0) :
    ∃ a : E → P2, (N.closedStar p).AffineOnFaces a ∧
      InjOn a (N.closedStar p).space ∧
      a p ∈ interior (a '' (N.closedStar p).space) := by
  let pi : V3 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.proj 1).prod (ContinuousLinearMap.proj 2)).toContinuousAffineMap
  let a : E → P2 := pi ∘ f
  let j : P2 → V3 := fun z => ![0, z.1, z.2]
  have hj : Continuous j := by
    fun_prop
  have hstar := K.closedStar_space_eq_inter_of_full N hK hNK hfull hp
  have hNKstar : N.closedStar p ≤ K.closedStar p :=
    fun _ hs => ⟨hNK hs.1, hNK hs.2⟩
  have hplane {x : E} (hx : x ∈ (N.closedStar p).space) : j (a x) = f x := by
    have hx' := hstar.subset hx
    have h0 := (hzero x hx'.1).mp hx'.2
    funext i
    fin_cases i
    · exact h0.symm
    · rfl
    · rfl
  have hpre : j ⁻¹' (f '' (K.closedStar p).space) = a '' (N.closedStar p).space := by
    ext z
    constructor
    · rintro ⟨x, hx, hfx⟩
      have hxN : x ∈ N.space := (hzero x hx).mpr (by rw [hfx]; rfl)
      refine ⟨x, hstar.symm.subset ⟨hx, hxN⟩, ?_⟩
      change pi (f x) = z
      rw [hfx]
      exact Prod.ext rfl rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (hstar.subset hx).1, (hplane hx).symm⟩
  have hpstar : p ∈ (N.closedStar p).space := by
    apply (N.closedStar p).vertices_subset_space
    have hpface : {p} ∈ N.faces := hp
    exact ⟨hpface, by simpa using hpface⟩
  have hfN : (N.closedStar p).AffineOnFaces f := fun s hs => hf s (hNKstar hs)
  refine ⟨a, hfN.postcomp pi, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hfi (hstar.subset hx).1 (hstar.subset hy).1
      ((hplane hx).symm.trans ((congrArg j hxy).trans (hplane hy)))
  · have hopen : IsOpen (j ⁻¹' interior (f '' (K.closedStar p).space)) :=
      isOpen_interior.preimage hj
    have hsub : j ⁻¹' interior (f '' (K.closedStar p).space) ⊆
        a '' (N.closedStar p).space := fun z hz =>
      hpre.subset (interior_subset (s := f '' (K.closedStar p).space) hz)
    apply interior_maximal hsub hopen
    change j (a p) ∈ interior (f '' (K.closedStar p).space)
    rwa [hplane hpstar]

theorem surface_incidence_of_flat_ambient_stars
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ N.vertices) → s ∈ N.faces)
    (hstars : ∀ p : N.vertices, ∃ f : E → V3,
      (K.closedStar p).AffineOnFaces f ∧ InjOn f (K.closedStar p).space ∧
      f p ∈ interior (f '' (K.closedStar p).space) ∧
      ∀ x ∈ (K.closedStar p).space, x ∈ N.space ↔ (f x) 0 = 0) :
    (∀ s ∈ N.faces, ∃ t ∈ N.faces, s ⊆ t ∧ t.card = 3) ∧
    (∀ s ∈ N.faces, s.card = 2 → (N.faceLink s).vertices.ncard = 2) := by
  have hN : N.faces.Finite := hK.subset hNK
  have hplanar : ∀ p : E, {p} ∈ N.faces → ∃ a : E → P2,
      (N.closedFaceStar {p}).AffineOnFaces a ∧
      InjOn a (N.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (N.closedFaceStar {p}).space) := by
    intro p hp
    obtain ⟨f, hf, hfi, hint, hzero⟩ := hstars ⟨p, hp⟩
    simpa only [closedFaceStar_singleton_eq_closedStar] using
      K.exists_planar_star_of_flat_ambient_star N hK hNK hfull hp f hf hfi hint hzero
  constructor
  · simpa using N.exists_full_coface_of_faceAffine_vertex_stars hN hplanar
  · simpa using N.faceLink_ncard_eq_two_of_faceAffine_vertex_stars hN hplanar

end Geometry.SimplicialComplex
