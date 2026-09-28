import PoincareConjecture.Proofs.M76.Mathlib.InteriorFullCofaces

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hasTwoFullCofaces_of_mem_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = Module.finrank ℝ E) {x : E}
    (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxint : x ∈ interior K.space) :
    K.HasTwoFullCofaces (Module.finrank ℝ E) s := by
  classical
  obtain ⟨t, ht, hst, htcard⟩ :=
    K.exists_full_coface_of_hull_meets_interior hK hs
      ⟨x, intrinsicInterior_subset hxs, hxint⟩
  obtain ⟨p, hps, hpt⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hst (show s.card + 1 = t.card by omega))
  have hptmem : p ∈ t := by rw [← hpt]; exact Finset.mem_insert_self p s
  let i : t := ⟨p, hptmem⟩
  let b : AffineBasis t ℝ E := (K.indep ht).affineBasisOfCard htcard
  have hcoord : EqOn (b.coord i) (AffineMap.const ℝ E 0) (s : Set E) := by
    intro v hv
    have hiv : i ≠ (⟨v, hst hv⟩ : t) := by
      intro he
      have hpv : p = v := congrArg Subtype.val he
      exact hps (hpv.symm ▸ hv)
    change b.coord i (b ⟨v, hst hv⟩) = 0
    exact b.coord_apply_ne hiv
  have hxi : b.coord i x = 0 := AffineMap.eqOn_affineSpan hcoord
    (convexHull_subset_affineSpan _ (intrinsicInterior_subset hxs))
  let T : Set (Finset E) := {u | u ∈ K.faces ∧ x ∉ convexHull ℝ (u : Set E)}
  have hT : T.Finite := hK.subset (fun _ hu => hu.1)
  let B : Set E := ⋃ u ∈ T, convexHull ℝ (u : Set E)
  have hB : IsClosed B :=
    (hT.isCompact_biUnion (fun u _ => u.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hxB : x ∉ B := by
    intro hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    exact hu.2 hxu
  let U := interior K.space \ B
  have hU : IsOpen U := isOpen_interior.sdiff hB
  have hxU : x ∈ U := ⟨hxint, hxB⟩
  have hxrel : x ∈ intrinsicInterior ℝ U :=
    interior_subset_intrinsicInterior (hU.interior_eq.symm ▸ hxU)
  have hdir : x - b i ∈ (affineSpan ℝ U).direction := by
    rw [hU.affineSpan_eq_top ⟨x, hxU⟩, AffineSubspace.direction_top]
    trivial
  obtain ⟨r, hr, hrU⟩ := exists_pos_smul_add_mem_of_intrinsicInterior hxrel hdir
  let z := r • (x - b i) + x
  have hzi : b.coord i z = -r := by
    change b.coord i (r • (x -ᵥ b i) +ᵥ x) = -r
    rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub,
      hxi, b.coord_apply_eq]
    simp
  obtain ⟨u, hu, hucard, hzu⟩ := K.exists_full_face_of_mem_interior hK hrU.1
  have hxu : x ∈ convexHull ℝ (u : Set E) := by
    by_contra hnot
    exact hrU.2 (mem_iUnion₂.mpr ⟨u, ⟨hu, hnot⟩, hzu⟩)
  have hsu : s ⊆ u := K.subset_of_mem_intrinsicInterior_face hs hu hxs hxu
  refine ⟨t, ht, u, hu, hst, hsu, htcard, hucard, ?_⟩
  intro htu
  have hzt : z ∈ convexHull ℝ (range b) := by
    simpa only [b, AffineIndependent.range_affineBasisOfCard, htu] using hzu
  have hnonneg := (b.convexHull_eq_nonneg_coord ▸ hzt) i
  rw [hzi] at hnonneg
  linarith

theorem hasTwoFullCofaces_of_intrinsicInterior_mem_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (_hcv : Convex ℝ K.space) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = Module.finrank ℝ E) {x : E}
    (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxint : x ∈ interior K.space) :
    K.HasTwoFullCofaces (Module.finrank ℝ E) s :=
  K.hasTwoFullCofaces_of_mem_interior hK hs hcard hxs hxint

theorem hasTwoFullCofaces_of_hull_meets_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = Module.finrank ℝ E)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior K.space).Nonempty) :
    K.HasTwoFullCofaces (Module.finrank ℝ E) s := by
  obtain ⟨x, hxs, hxint⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      isOpen_interior hmeet
  exact K.hasTwoFullCofaces_of_intrinsicInterior_mem_interior hK hcv hs hcard hxs hxint

end Geometry.SimplicialComplex
