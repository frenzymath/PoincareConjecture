import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Exposed.EdgeVertices

/-!
# Whole-side classification at retained boundary joins

An unpaired coordinate side cannot pass through any retained vertex in
its open part. If two closed boundary arcs meet only at retained joins,
the connected open side lies wholly in one arc, and closedness restores
its endpoints. This supplies the side classification for Morgan--Tian,
Claim 19.39 and Lemma 19.46, pp. 470 and 474-475. See
`proof-work/tasks/M64/derivations/2026-09-25-boundary-arc-turning.md`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- An actual unpaired coordinate side covered by two closed arc images
lies wholly in one of them when their intersections are retained vertices.
This proves the whole-side classification used in Morgan--Tian,
Claim 19.39 and Lemma 19.46, pp. 470 and 474-475. -/
theorem m64Intrinsic_unpaired_side_subset_one_of_two_arcs
    {I : Type*} (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i v)})
    (p : I × Fin 3)
    (hunpaired : ∀ q : I × Fin 3,
      faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p)
    {A B : Set AnnulusCoordinates} (hA : IsClosed A) (hB : IsClosed B)
    (himage : ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ A ∪ B)
    (v0 v1 : Euler.CoordinateVertex F b) (hAB : A ∩ B ⊆ {v0.1, v1.1}) :
    ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ A ∨
      ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ B := by
  let eta := ((face p.1).boundary p.2).map
  let e := faceBoundaryIndex face p.1 p.2
  have hout : e.out = p := hunpaired e.out (Quotient.out_eq e)
  have hcanonical : faceBoundaryEdge face e = (face p.1).boundary p.2 := by
    change (face e.out.1).boundary e.out.2 = _
    rw [hout]
  have he : Nat.card {q : I × Fin 3 // faceBoundaryIndex face q.1 q.2 = e} = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨?_⟩, ⟨⟨p, rfl⟩⟩⟩
    intro q r
    exact Subtype.ext ((hunpaired q.1 q.2).trans (hunpaired r.1 r.2).symm)
  have hinj : InjOn eta (Icc (0 : ℝ) 1) :=
    m64Intrinsic_coordinate_boundary_injective face F b hsource hboundary p.1 p.2
  have hvertex (v : Euler.CoordinateVertex F b) {t : ℝ}
      (ht : t ∈ Ioo (0 : ℝ) 1) : eta t ≠ v.1 := by
    intro htv
    have hmem : v.1 ∈ (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1 := by
      rw [hcanonical]
      exact ⟨t, Ioo_subset_Icc_self ht, htv⟩
    have hv := (m64Intrinsic_vertex_on_one_face_edge_iff_endpoint face F b hsource hcarrier
      hboundary hinter e he v).mp hmem
    rw [hcanonical] at hv
    rcases hv with hv | hv
    · exact ht.1.ne' (hinj (Ioo_subset_Icc_self ht) (by simp) (htv.trans hv))
    · exact ht.2.ne (hinj (Ioo_subset_Icc_self ht) (by simp) (htv.trans hv))
  have havoid (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : eta t ∉ A ∩ B := by
    intro h
    rcases mem_insert_iff.mp (hAB h) with h0 | h1
    · exact hvertex v0 ht h0
    · exact hvertex v1 ht (mem_singleton_iff.mp h1)
  have hcont : ContinuousOn eta (Icc (0 : ℝ) 1) :=
    ((face p.1).boundary p.2).smooth.continuousOn
  have hconnected : IsPreconnected (eta '' Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image eta (hcont.mono Ioo_subset_Icc_self)
  have hcover : eta '' Ioo (0 : ℝ) 1 ⊆ A ∪ B :=
    (image_mono Ioo_subset_Icc_self).trans himage
  have hside : eta '' Ioo (0 : ℝ) 1 ⊆ A ∨ eta '' Ioo (0 : ℝ) 1 ⊆ B := by
    by_cases hmeet : (eta '' Ioo (0 : ℝ) 1 ∩ A).Nonempty
    · left
      intro z hz
      by_contra hzA
      have hzB := (hcover hz).resolve_left hzA
      obtain ⟨w, ⟨t, ht, rfl⟩, hwA, hwB⟩ :=
        isPreconnected_closed_iff.mp hconnected A B hA hB hcover hmeet ⟨z, hz, hzB⟩
      exact havoid t ht ⟨hwA, hwB⟩
    · right
      intro z hz
      exact (hcover hz).resolve_left (fun hzA => hmeet ⟨z, hz, hzA⟩)
  have hfull {C : Set AnnulusCoordinates} (hC : IsClosed C)
      (hsub : eta '' Ioo (0 : ℝ) 1 ⊆ C) : eta '' Icc (0 : ℝ) 1 ⊆ C := by
    rintro z ⟨t, ht, rfl⟩
    have htclosure : t ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo zero_ne_one]
      exact ht
    have h := ((hcont t ht).mono Ioo_subset_Icc_self).mem_closure htclosure
      (fun s hs => hsub ⟨s, hs, rfl⟩)
    simpa only [hC.closure_eq] using h
  exact hside.elim (fun h => Or.inl (hfull hA h)) (fun h => Or.inr (hfull hB h))

end PoincareMT
