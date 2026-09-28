import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedDomainChartStars
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X] [T2Space X]

local notation "V3" => (Fin 3 → ℝ)

private theorem open_edge_mem_intrinsicInterior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p q x : E} (hpq : p ≠ q) (he : ({p, q} : Finset E) ∈ K.faces)
    (hx : x ∈ openSegment ℝ p q) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (({p, q} : Finset E) : Set E)) := by
  have hxh : x ∈ convexHull ℝ (({p, q} : Finset E) : Set E) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      openSegment_subset_segment ℝ p q hx
  obtain ⟨a, ha, hxa⟩ :=
    K.exists_face_intrinsicInterior_of_finite hK (K.convexHull_subset_space he hxh)
  have hsub : a ⊆ {p, q} := K.subset_of_mem_intrinsicInterior_face ha he hxa hxh
  have heq : a = {p, q} := by
    by_contra hne
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hpair : ({p, q} : Finset E).card = 2 := by simp [hpq]
    have hpos := (K.nonempty_of_mem_faces ha).card_pos
    have hcard : a.card = 1 := by omega
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hxz : x = z := by
      simpa only [hz, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff]
        using intrinsicInterior_subset hxa
    have hzp : z = p ∨ z = q := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        hsub (hz.symm ▸ Finset.mem_singleton_self z)
    rcases hzp with h | h
    · exact hpq ((left_mem_openSegment_iff).mp ((hxz.trans h) ▸ hx))
    · exact hpq ((right_mem_openSegment_iff).mp ((hxz.trans h) ▸ hx))
  exact heq ▸ hxa

omit [T2Space X] in



theorem exists_original_edge_coordinates
    (K : SimplicialComplex ℝ E) (g : E → X) (hg : InjOn g K.space)
    (e : ι → OpenPartialHomeomorph X V3)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (p q : E) (hpq : p ≠ q) (hpqK : ({p, q} : Finset E) ∈ K.faces) :
    ∃ B : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (segment ℝ p q) B.source ∧ B (g p) ≠ B (g q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        AffineMap.lineMap (B (g p)) (B (g q)) t ∈ B.target ∧
        B.symm (AffineMap.lineMap (B (g p)) (B (g q)) t) =
          g (AffineMap.lineMap p q t)) ∧
      B.symm '' segment ℝ (B (g p)) (B (g q)) = g '' segment ℝ p q := by
  obtain ⟨B, hmap, hB, hface⟩ :=
    hstars p (K.face_subset_vertices hpqK (Finset.mem_insert_self _ _))
  have hstar : ({p, q} : Finset E) ∈ (K.closedStar p).faces := by
    refine ⟨hpqK, ?_⟩
    simpa only [Finset.insert_idem] using hpqK
  have hstarSeg : segment ℝ p q ⊆ (K.closedStar p).space := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      (K.closedStar p).convexHull_subset_space hstar
  have hseg : segment ℝ p q ⊆ K.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space hpqK
  have hsource : MapsTo g (segment ℝ p q) B.source := hmap.mono_left hstarSeg
  have hpB := hsource (left_mem_segment ℝ p q)
  have hqB := hsource (right_mem_segment ℝ p q)
  have hne : B (g p) ≠ B (g q) := by
    intro h
    exact hpq (hg (hseg (left_mem_segment ℝ p q)) (hseg (right_mem_segment ℝ p q))
      (B.injOn hpB hqB h))
  obtain ⟨A, hA⟩ := hface _ hstar
  have hAseg : EqOn (B ∘ g) A (segment ℝ p q) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hA
  have hcoord (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      B (g (AffineMap.lineMap p q t)) = AffineMap.lineMap (B (g p)) (B (g q)) t := by
    change (B ∘ g) (AffineMap.lineMap p q t) = _
    rw [hAseg (lineMap_mem_segment ℝ p q ht)]
    change A.toAffineMap (AffineMap.lineMap p q t) = _
    rw [A.toAffineMap.apply_lineMap]
    change AffineMap.lineMap (A p) (A q) t = _
    rw [← hAseg (left_mem_segment ℝ p q), ← hAseg (right_mem_segment ℝ p q)]
    rfl
  have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap (B (g p)) (B (g q)) t ∈ B.target ∧
      B.symm (AffineMap.lineMap (B (g p)) (B (g q)) t) =
        g (AffineMap.lineMap p q t) := by
    rw [← hcoord t ht]
    have hs := hsource (lineMap_mem_segment ℝ p q ht)
    exact ⟨B.map_source hs, B.left_inv hs⟩
  refine ⟨B, hB, hsource, hne, hparameter, ?_⟩
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image, image_image]
  exact image_congr (fun t ht => (hparameter t ht).2)





theorem exists_original_edge_open_protection
    (K M : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hMK : M ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (Z : Set X) (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    (p q : E) (hpq : p ≠ q) (hpqK : ({p, q} : Finset E) ∈ K.faces)
    (hpqM : ({p, q} : Finset E) ∉ M.faces) :
    ∃ U : Set X, IsOpen U ∧ MapsTo g (openSegment ℝ p q) U ∧
      Disjoint U Z ∧ Disjoint U (g '' K.vertices) ∧
      ∀ a ∈ K.faces, a.card = 2 → a ≠ {p, q} →
        Disjoint U (g '' convexHull ℝ (a : Set E)) := by
  classical
  let T : Set (Finset E) := {a | a ∈ K.faces ∧ a.card = 2 ∧ a ≠ {p, q}}
  have hT : T.Finite := hK.subset (fun _ ha => ha.1)
  have hV : K.vertices.Finite := by
    rw [K.vertices_eq]
    exact hK.biUnion (fun a _ => a.finite_toSet)
  let C := (g '' K.vertices) ∪ ⋃ a ∈ T, g '' convexHull ℝ (a : Set E)
  have hC : IsCompact C := (hV.image g).isCompact.union
    (hT.isCompact_biUnion fun a ha =>
      (a.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
        (hgc.mono (K.convexHull_subset_space ha.1)))
  have hseg : segment ℝ p q ⊆ K.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space hpqK
  let U := Zᶜ ∩ Cᶜ
  refine ⟨U, hZ.isOpen_compl.inter hC.isClosed.isOpen_compl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxK := hseg (openSegment_subset_segment ℝ p q hx)
    have hxi := open_edge_mem_intrinsicInterior K hK hpq hpqK hx
    refine ⟨?_, ?_⟩
    · intro hxZ
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp ((hmark x hxK).mp hxZ)
      have hsub := K.subset_of_mem_intrinsicInterior_face hpqK (hMK ha) hxi hxa
      exact hpqM (M.down_closed ha hsub (Finset.insert_nonempty _ _))
    · intro hxC
      rcases hxC with ⟨y, hy, hgy⟩ | hxC
      · have hyx := hgi (K.vertices_subset_space hy) hxK hgy
        have hxv : x ∈ K.vertices := hyx ▸ hy
        have hxp : x = p ∨ x = q := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using
            (K.vertex_mem_convexHull_iff hxv hpqK).mp (intrinsicInterior_subset hxi)
        rcases hxp with rfl | rfl
        · exact hpq (left_mem_openSegment_iff.mp hx)
        · exact hpq (right_mem_openSegment_iff.mp hx)
      · obtain ⟨a, ha, y, hy, hgy⟩ := mem_iUnion₂.mp hxC
        have hyx := hgi (K.convexHull_subset_space ha.1 hy) hxK hgy
        have hsub := K.subset_of_mem_intrinsicInterior_face hpqK ha.1 hxi (hyx ▸ hy)
        have hcard : a.card ≤ ({p, q} : Finset E).card := by simp [ha.2.1, hpq]
        exact ha.2.2 (Finset.eq_of_subset_of_card_le hsub hcard).symm
  · exact disjoint_left.mpr (fun _ hx hz => hx.1 hz)
  · exact disjoint_left.mpr (fun _ hx hv => hx.2 (Or.inl hv))
  · intro a ha hac hne
    exact disjoint_left.mpr fun _ hx hy =>
      hx.2 (Or.inr (mem_iUnion₂.mpr ⟨a, ⟨ha, hac, hne⟩, hy⟩))

end Geometry.SimplicialComplex
