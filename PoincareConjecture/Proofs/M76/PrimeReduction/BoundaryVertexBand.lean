import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexRimCover
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {K L : SimplicialComplex ℝ E}
  [Fintype K.faces] [Fintype L.faces] {T : BoundaryTriangleFibers K L}

local notation "I" => Icc (0 : ℝ) 1

open Classical in

theorem BoundaryEdgeFamily.exists_vertex_band (P : BoundaryEdgeFamily T)
    (hLK : L ≤ K) (hLcard : ∀ u ∈ L.faces, u.card ≤ 3)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    {p : E} (hp : p ∈ L.vertices) :
    let B := ((K.barycentricDualBlock {p}).link p).space
    let W := (L.barycentricDualBlock {p}).space
    let q := B ∩ W
    ∃ f : E × ℝ → E, FinitePiecewiseAffineOn f (q ×ˢ I) ∧
      InjOn f (q ×ˢ I) ∧ MapsTo f (q ×ˢ I) B ∧
      (∀ x ∈ q, f (x, 0) = x) ∧
      (∀ x ∈ q ×ˢ I, f x ∈ W ↔ x.2 = 0) ∧
      (∀ s ∈ L.faces, s.card = 2 → p ∈ s →
        ∀ x ∈ (L.barycentricDualBlock s).space ×ˢ I, f x = P.map s x) := by
  classical
  let B := ((K.barycentricDualBlock {p}).link p).space
  let W := (L.barycentricDualBlock {p}).space
  let q := B ∩ W
  let J := {s : Finset E // s ∈ L.faces ∧ s.card = 2 ∧ p ∈ s}
  have hJset : {s : Finset E | s ∈ L.faces ∧ s.card = 2 ∧ p ∈ s}.Finite :=
    (Set.toFinite L.faces).subset (fun _ hs => hs.1)
  let : Finite J := hJset.to_subtype
  let S : J → Set E := fun s => (L.barycentricDualBlock s).space
  have htarget (s : J) : (K.barycentricDualBlock s).space ⊆ B :=
    K.boundary_edge_dual_subset_vertex_link L hLK hp s.property.2.1 s.property.2.2
  have hSq (s : J) : S s ⊆ q := by
    intro x hx
    exact ⟨htarget s (space_subset_of_le
      (K.barycentricDualBlock_mono_of_subcomplex L hLK s) hx),
      space_subset_of_le (L.barycentricDualBlock_antitone
        (Finset.singleton_subset_iff.mpr s.property.2.2)) hx⟩
  have hcover : (⋃ s : J, S s) = q := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact hSq s hs
    · intro x hx
      have hx' := (K.boundary_vertex_rim_eq_iUnion_edges L hLK hp).subset
        ⟨hx.2, hx.1⟩
      simp only [mem_iUnion] at hx'
      obtain ⟨s, hs, hc, hp, hx⟩ := hx'
      exact mem_iUnion.mpr ⟨⟨s, hs, hc, hp⟩, hx⟩
  have hcoverI : (⋃ s : J, S s ×ˢ I) = q ×ˢ I := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact ⟨hcover.subset (mem_iUnion.mpr ⟨s, hs.1⟩), hs.2⟩
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp (hcover.symm.subset hx.1)
      exact mem_iUnion.mpr ⟨s, hs, hx.2⟩
  have hagree (s t : J) (x : E × ℝ) (hx : x ∈ S s ×ˢ I)
      (hy : x ∈ S t ×ˢ I) : P.map s x = P.map t x :=
    P.agrees hLK hLcard hfull s.property.1 t.property.1
      s.property.2.1 t.property.2.1 x ⟨⟨hx.1, hy.1⟩, hx.2⟩
  have hinjective (s t : J) (x y : E × ℝ) (hx : x ∈ S s ×ˢ I)
      (hy : y ∈ S t ×ˢ I) (he : P.map s x = P.map t y) : x = y := by
    have hxN := (P.image_eq s s.property.1 s.property.2.1).subset ⟨x, hx, rfl⟩
    have hyN : P.map s x ∈ (K.barycentricDualBlock t).space := he.symm ▸
      (P.image_eq t t.property.1 t.property.2.1).subset ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzx⟩ := (P.overlap_image hLK hLcard hfull
      s.property.1 t.property.1 s.property.2.1 t.property.2.1).symm.subset ⟨hxN, hyN⟩
    have hzx' : z = x := P.injective s s.property.1 s.property.2.1
      ⟨hz.1.1, hz.2⟩ hx hzx
    subst z
    exact P.injective t t.property.1 t.property.2.1 ⟨hz.1.2, hz.2⟩ hy
      ((hagree s t x hx ⟨hz.1.2, hz.2⟩).symm.trans he)
  let f : E × ℝ → E := fun x => if hx : x ∈ ⋃ s : J, S s ×ˢ I then
    P.map (mem_iUnion.mp hx).choose x else 0
  have hvalue (s : J) (x : E × ℝ) (hx : x ∈ S s ×ˢ I) : f x = P.map s x := by
    have hu : x ∈ ⋃ s : J, S s ×ˢ I := mem_iUnion.mpr ⟨s, hx⟩
    dsimp only [f]
    rw [dif_pos hu]
    exact hagree _ s x (mem_iUnion.mp hu).choose_spec hx
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcoverI]
    exact FinitePiecewiseAffineOn.iUnion fun s =>
      (P.piecewiseAffine s s.property.1 s.property.2.1).congr
        (fun x hx => (hvalue s x hx).symm)
  · intro x hx y hy he
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    obtain ⟨t, ht⟩ := mem_iUnion.mp (hcoverI.symm.subset hy)
    exact hinjective s t x y hs ht ((hvalue s x hs).symm.trans (he.trans (hvalue t y ht)))
  · intro x hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    rw [hvalue s x hs]
    exact htarget s ((P.image_eq s s.property.1 s.property.2.1).subset ⟨x, hs, rfl⟩)
  · intro x hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    exact (hvalue s (x, 0) ⟨hs, by norm_num⟩).trans
      (P.central s s.property.1 s.property.2.1 x hs)
  · intro x hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    rw [hvalue s x hs]
    constructor
    · intro hy
      exact (P.boundary s s.property.1 s.property.2.1 x hs).mp
        (L.barycentricSubdivision_isSubdivision.space_eq.subset
          (space_subset_of_le (L.barycentricDualBlock_le {p}) hy))
    · intro ht
      have he : x = (x.1, 0) := Prod.ext rfl ht
      rw [he, P.central s s.property.1 s.property.2.1 _ hs.1]
      exact (hSq s hs.1).2
  · intro s hs hc hp x hx
    exact hvalue ⟨s, hs, hc, hp⟩ x hx

end Geometry.SimplicialComplex
