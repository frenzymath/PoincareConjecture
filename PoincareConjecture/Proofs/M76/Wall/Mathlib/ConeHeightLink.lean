import PoincareConjecture.Proofs.M76.Wall.Mathlib.PiecewiseVertexSuperlevel
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {f : E → ℝ}

theorem AffineOnFaces.closedStar_link_level (hf : K.AffineOnFaces f)
    (p : E) (r : ℝ) (hstar : K.closedStar p = K) (hp : r < f p)
    (hother : ∀ v ∈ K.vertices, v ≠ p → f v = r) :
    (∀ x ∈ K.space, r ≤ f x) ∧
      (K.link p).space = K.space ∩ {x | f x = r} := by
  have hvertices (v : E) (hv : v ∈ K.vertices) : r ≤ f v := by
    by_cases h : v = p
    · subst v
      exact hp.le
    · exact (hother v hv h).ge
  have hlower (x : E) (hx : x ∈ K.space) : r ≤ f x := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := hf s hs
    have hverts : (s : Set E) ⊆ a ⁻¹' Ici r := by
      intro v hv
      change r ≤ a v
      rw [← ha (subset_convexHull ℝ _ hv)]
      exact hvertices v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v))
    have hax : r ≤ a x :=
      convexHull_min hverts ((convex_Ici r).affine_preimage a.toAffineMap) hxs
    rwa [← ha hxs] at hax
  have hneg : K.AffineOnFaces (fun x => -f x) :=
    hf.postcomp (-ContinuousAffineMap.id ℝ ℝ)
  have hsuper := hneg.vertexSuperlevel_space (-r) (by
    intro s hs
    apply Or.inl
    intro v hv
    exact neg_le_neg (hvertices v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))))
  have hcomplex : K.vertexSubcomplex {x | -r ≤ -f x} = K.link p := by
    ext s
    constructor
    · intro hs
      have hcone : s ∈ (K.closedStar p).faces := hstar.symm ▸ hs.1
      refine ⟨hs.1, ?_, hcone.2⟩
      intro hps
      have h := hs.2 p hps
      change -r ≤ -f p at h
      linarith
    · intro hs
      refine ⟨hs.1, ?_⟩
      intro v hv
      have hvp : v ≠ p := fun he => hs.2.1 (he ▸ hv)
      change -r ≤ -f v
      rw [hother v (K.down_closed hs.1 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)) hvp]
  rw [hcomplex] at hsuper
  refine ⟨hlower, ?_⟩
  rw [hsuper]
  ext x
  constructor
  · rintro ⟨hx, hnegx⟩
    have hxlow := hlower x hx
    refine ⟨hx, ?_⟩
    change -r ≤ -f x at hnegx
    change f x = r
    exact le_antisymm (neg_le_neg_iff.mp hnegx) hxlow
  · rintro ⟨hx, hfx⟩
    exact ⟨hx, by change -r ≤ -f x; rw [hfx]⟩

end Geometry.SimplicialComplex
