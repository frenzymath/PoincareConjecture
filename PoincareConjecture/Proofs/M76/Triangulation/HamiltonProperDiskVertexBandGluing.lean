import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBand
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFrontierProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexRimCover
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}
  {C : HamiltonProperDiskCoherentSides T c}




theorem HamiltonProperDiskLowerProducts.exists_vertex_band
    (P : HamiltonProperDiskLowerProducts T C)
    (hproper : ∀ x : closedBall (0 : V2) 1,
      (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (p : T.disk.vertices) : Nonempty (HamiltonProperDiskVertexBand P p) := by
  classical
  let q := T.dualRegionRim {(p : E)} ∩ D
  let Q := T.dualRegionRim {(p : E)}
  let A := T.diskVertexBlock p ∩ frontier R
  let J := {s : Finset E // s ∈ T.disk.faces ∧ 2 ≤ s.card ∧ (p : E) ∈ s}
  have hJset : {s : Finset E | s ∈ T.disk.faces ∧ 2 ≤ s.card ∧ (p : E) ∈ s}.Finite :=
    (T.finite.subset T.disk_le).subset (fun _ hs => hs.1)
  let : Finite J := hJset.to_subtype
  let K := J ⊕ PLift ((p : E) ∈ frontier R)
  let G : ((p : E) ∈ frontier R) → HamiltonProperDiskFrontierProduct P p :=
    fun hp => Classical.choice (P.exists_frontier_vertex_product hproper p hp)
  let S : K → Set E := fun i => match i with
    | .inl s => T.diskDualBase s
    | .inr _ => A
  let f : K → E × ℝ → E := fun i => match i with
    | .inl s => P.map s
    | .inr h => (G h.down).map
  have hqB : q ⊆ T.diskVertexBlock p := (T.vertex_base_ballPair p).1
  have hAQ : A ⊆ q := by
    change A ⊆ T.dualRegionRim {(p : E)} ∩ D
    rw [T.vertex_base_rim_eq]
    exact subset_union_right
  have hstrict (s : J) : {(p : E)} ⊂ (s : Finset E) := by
    apply (Finset.singleton_subset_iff.mpr s.property.2.2).ssubset_of_ne
    intro he
    have hc := s.property.2.1
    rw [← he, Finset.card_singleton] at hc
    omega
  have htarget (s : J) : T.dualRegion s ⊆ Q :=
    T.dualRegion_subset_rim_of_ssubset p.property s.property.1 (hstrict s)
  have hSq (i : K) : S i ⊆ q := by
    rcases i with s | h
    · exact fun _ hx => ⟨htarget s hx.1, hx.2⟩
    · exact hAQ
  have hfrontp {x : E} (hxN : x ∈ (T.vertexBlock p).space)
      (hxF : x ∈ frontier R) : (p : E) ∈ frontier R := by
    by_contra hn
    exact hxF.2 (T.vertexBlock_subset_interior p hn hxN)
  have hcover : (⋃ i : K, S i) = q := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hSq i hi
    · intro x hx
      rw [show q = T.dualRegionRim {(p : E)} ∩ D from rfl,
        T.vertex_base_rim_eq_edges_union_frontier] at hx
      rcases hx with hx | hx
      · simp only [mem_iUnion] at hx
        obtain ⟨s, hs, hc, hp, hx⟩ := hx
        exact mem_iUnion.mpr ⟨Sum.inl ⟨s, hs, by omega, hp⟩, hx⟩
      · have hp := hfrontp ((T.diskVertexBlock_eq_inter p).subset hx.1).1 hx.2
        exact mem_iUnion.mpr ⟨Sum.inr ⟨hp⟩, hx⟩
  have hcoverI : (⋃ i : K, S i ×ˢ I) = q ×ˢ I := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨hcover.subset (mem_iUnion.mpr ⟨i, hi.1⟩), hi.2⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hx.1)
      exact mem_iUnion.mpr ⟨i, hi, hx.2⟩
  have hfaceFront (s : J) {x : E} (hx : x ∈ T.diskDualBase s)
      (hxF : x ∈ frontier R) :
      (s : Finset E) ∈ T.boundary.faces ∧ (s : Finset E).card = 2 ∧
        x = (s : Finset E).centroid ℝ id := by
    have hsF : (s : Finset E) ∈ T.boundary.faces := by
      by_contra hn
      exact (T.nonboundary_base_contact_empty s.property.1 hn).subset ⟨hx, hxF⟩
    have hle := T.disk_face_card_le s.property.1
    have hlo := s.property.2.1
    have hne : (s : Finset E).card ≠ 3 :=
      fun hc => T.disk_triangle_not_boundary hproper s.property.1 hc hsF
    have hc : (s : Finset E).card = 2 := by omega
    exact ⟨hsF, hc, (T.boundary_edge_base_contact hproper s.property.1 hc hsF).subset
      ⟨hx, hxF⟩⟩
  have hcrossAgree (s : J) (h : PLift ((p : E) ∈ frontier R))
      (x : E × ℝ) (hx : x ∈ S (.inl s) ×ˢ I) (hy : x ∈ S (.inr h) ×ˢ I) :
      f (.inl s) x = f (.inr h) x := by
    obtain ⟨hsF, hc, hcenter⟩ := hfaceFront s hx.1 hy.1.2
    have he : x = ((s : Finset E).centroid ℝ id, x.2) := Prod.ext hcenter rfl
    change P.map s x = (G h.down).map x
    rw [he]
    exact ((G h.down).keep_edge s s.property.1 hsF s.property.2.2 hc x.2 hx.2).symm
  have hagree (i j : K) (x : E × ℝ) (hx : x ∈ S i ×ˢ I) (hy : x ∈ S j ×ˢ I) :
      f i x = f j x := by
    rcases i with s | h <;> rcases j with t | k
    · exact P.agrees s s.property.1 s.property.2.1 t t.property.1 t.property.2.1
        x ⟨⟨hx.1, hy.1⟩, hx.2⟩
    · exact hcrossAgree s k x hx hy
    · exact (hcrossAgree t h x hy hx).symm
    · rfl
  have hlocalPL (i : K) : FinitePiecewiseAffineOn (f i) (S i ×ˢ I) := by
    rcases i with s | h
    · exact P.piecewiseAffine s s.property.1 s.property.2.1
    · exact (G h.down).piecewiseAffine
  have hlocalInside (i : K) : MapsTo (f i) (S i ×ˢ I) Q := by
    rcases i with s | h
    · intro x hx
      exact htarget s ((P.image_eq s s.property.1 s.property.2.1).subset ⟨x, hx, rfl⟩)
    · intro x hx
      have hF := (G h.down).image_eq.subset ⟨x, hx, rfl⟩
      exact Or.inr hF
  have hlocalCentral (i : K) (x : E) (hx : x ∈ S i) : f i (x, 0) = x := by
    rcases i with s | h
    · exact P.central s s.property.1 s.property.2.1 x hx
    · exact (G h.down).central x hx
  have hlocalPos (i : K) (x : E × ℝ) (hx : x ∈ S i ×ˢ I) :
      0 ≤ C.labels.height p (f i x) ↔ 0 ≤ x.2 := by
    rcases i with s | h
    · exact P.positive s s.property.1 s.property.2.1 p s.property.2.2 x hx
    · exact (G h.down).positive x hx
  have hlocalNeg (i : K) (x : E × ℝ) (hx : x ∈ S i ×ˢ I) :
      C.labels.height p (f i x) ≤ 0 ↔ x.2 ≤ 0 := by
    rcases i with s | h
    · exact P.negative s s.property.1 s.property.2.1 p s.property.2.2 x hx
    · exact (G h.down).negative x hx
  have hlocalProper (i : K) (x : E × ℝ) (hx : x ∈ S i ×ˢ I) :
      f i x ∈ frontier R ↔ x.1 ∈ frontier R := by
    rcases i with s | h
    · exact P.proper s s.property.1 s.property.2.1 x hx
    · exact iff_of_true ((G h.down).image_eq.subset ⟨x, hx, rfl⟩).2 hx.1.2
  have hcrossInjective (s : J) (h : PLift ((p : E) ∈ frontier R))
      (x y : E × ℝ) (hx : x ∈ S (.inl s) ×ˢ I) (hy : y ∈ S (.inr h) ×ˢ I)
      (he : f (.inl s) x = f (.inr h) y) : x = y := by
    have hyF : f (.inr h) y ∈ frontier R :=
      ((G h.down).image_eq.subset ⟨y, hy, rfl⟩).2
    have hxF : x.1 ∈ frontier R := (hlocalProper (.inl s) x hx).mp (he.symm ▸ hyF)
    have hx' : x ∈ S (.inr h) ×ˢ I := ⟨⟨hqB (hSq (.inl s) hx.1), hxF⟩, hx.2⟩
    exact (G h.down).injective hx' hy ((hcrossAgree s h x hx hx').symm.trans he)
  have hlocalInjective (i j : K) (x y : E × ℝ)
      (hx : x ∈ S i ×ˢ I) (hy : y ∈ S j ×ˢ I) (he : f i x = f j y) : x = y := by
    rcases i with s | h <;> rcases j with t | k
    · change P.map s x = P.map t y at he
      have hy0 : P.map s x ∈ T.dualRegion s :=
        (P.image_eq s s.property.1 s.property.2.1).subset ⟨x, hx, rfl⟩
      have hy1 : P.map s x ∈ T.dualRegion t := he.symm ▸
        (P.image_eq t t.property.1 t.property.2.1).subset ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ :=
        (P.overlap_image s s.property.1 s.property.2.1
          t t.property.1 t.property.2.1).symm.subset ⟨hy0, hy1⟩
      have hzx' : z = x := P.injective s s.property.1 s.property.2.1
        ⟨hz.1.1, hz.2⟩ hx hzx
      subst z
      exact P.injective t t.property.1 t.property.2.1 ⟨hz.1.2, hz.2⟩ hy
        ((P.agrees s s.property.1 s.property.2.1 t t.property.1 t.property.2.1 x hz).symm.trans he)
    · exact hcrossInjective s k x y hx hy he
    · exact (hcrossInjective t h y x hy hx he.symm).symm
    · exact (G h.down).injective hx hy he
  let g : E × ℝ → E := fun x => if hx : x ∈ ⋃ i : K, S i ×ˢ I then
    f (mem_iUnion.mp hx).choose x else 0
  have hvalue (i : K) (x : E × ℝ) (hx : x ∈ S i ×ˢ I) : g x = f i x := by
    have hu : x ∈ ⋃ i : K, S i ×ˢ I := mem_iUnion.mpr ⟨i, hx⟩
    dsimp only [g]
    rw [dif_pos hu]
    exact hagree _ i x (mem_iUnion.mp hu).choose_spec hx
  have hgPL : FinitePiecewiseAffineOn g (q ×ˢ I) := by
    rw [← hcoverI]
    exact FinitePiecewiseAffineOn.iUnion fun i =>
      (hlocalPL i).congr (fun x hx => (hvalue i x hx).symm)
  refine ⟨{
    map := g
    piecewiseAffine := hgPL
    injective := ?_
    inside := ?_
    central := ?_
    positive := ?_
    negative := ?_
    proper := ?_
    keep_face := ?_
    frontier_image_subset := ?_ }⟩
  · intro x hx y hy he
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverI.symm.subset hy)
    exact hlocalInjective i j x y hi hj
      ((hvalue i x hi).symm.trans (he.trans (hvalue j y hj)))
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    rw [hvalue i x hi]
    exact hlocalInside i hi
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    exact (hvalue i (x, 0) ⟨hi, by norm_num⟩).trans (hlocalCentral i x hi)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    rw [hvalue i x hi]
    exact hlocalPos i x hi
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    rw [hvalue i x hi]
    exact hlocalNeg i x hi
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcoverI.symm.subset hx)
    rw [hvalue i x hi]
    exact hlocalProper i x hi
  · intro s hs hc hp x hx
    exact hvalue (.inl ⟨s, hs, hc, hp⟩) x hx
  · intro x hx
    have hp := hfrontp hx.1 hx.2
    obtain ⟨y, hy, hyx⟩ := (G hp).image_eq.symm.subset hx
    exact ⟨y, ⟨hAQ hy.1, hy.2⟩, (hvalue (.inr ⟨hp⟩) y hy).trans hyx⟩

end PoincareConjecture.M76.HamiltonIndexOne
