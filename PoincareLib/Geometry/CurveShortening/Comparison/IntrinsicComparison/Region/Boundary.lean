import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Region.Turning

/-!
# Unpaired sides are on the actual regional frontier

At an interior point of an unpaired side, compatible parent intersections
exclude every other face. The finite family is closed, so a neighborhood
of that point meets only its own face. It cannot be interior to the full
region. Continuity extends this conclusion to the two endpoints.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- Every full unpaired geometric side of a compatible finite family lies on the frontier of
its actual union. This identifies the support of the uncancelled turning terms using the
constructed geometric intersections. Source: Morgan--Tian Proposition 19.35, printed pp.
467-481, including the Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional
construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
theorem m64Intrinsic_unpaired_side_subset_region_frontier
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
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
      faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p) :
    ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
      frontier (⋃ i, (face i).carrier) := by
  classical
  rcases p with ⟨i, k⟩
  have hopen {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      ((face i).boundary k).map t ∈ frontier (⋃ j, (face j).carrier) := by
    let q := ((face i).boundary k).map t
    have hqedge : q ∈ ((face i).boundary k).map '' Icc (0 : ℝ) 1 :=
      mem_image_of_mem _ (Ioo_subset_Icc_self ht)
    have hqfront : q ∈ frontier (face i).carrier :=
      (face i).boundary_image_subset_frontier k hqedge
    have hqface : q ∈ (face i).carrier := (face i).isClosed_carrier.frontier_subset hqfront
    have hnotvertex (v : Fin 3) : q ≠ F i (b i v) := by
      intro hv
      have hv' : F i (affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)) t) =
          F i (b i v) := by
        change (F i ∘ affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1))) t = _
        rw [← hboundary]
        exact hv
      rcases Euler.coordinate_vertex_on_edge (F i) (b i) (hsource i) k v
        (Ioo_subset_Icc_self ht) hv' with hzero | hone
      · exact ht.1.ne' hzero
      · exact ht.2.ne hone
    have hother (j : I) (hji : j ≠ i) : q ∉ (face j).carrier := by
      intro hj
      rcases hinter i j hji.symm with ⟨k', l, hk, hl⟩ | ⟨v, hv⟩
      · by_cases hkk : k' = k
        · subst k'
          have he := (faceBoundaryIndex_eq_iff face j i l k).mpr hl.symm
          exact hji (congrArg Prod.fst (hunpaired (j, l) he))
        · have hqk' := hk ▸ (show q ∈ (face i).carrier ∩ (face j).carrier from ⟨hqface, hj⟩)
          rw [hboundary] at hqedge hqk'
          have hv := Euler.coordinate_distinct_edges (F i) (b i) (hsource i) k k'
            (Ne.symm hkk) ⟨hqedge, hqk'⟩
          rcases hv with hv | hv
          · exact hnotvertex _ hv
          · exact hnotvertex _ (mem_singleton_iff.mp hv)
      · exact hnotvertex v (mem_singleton_iff.mp (hv ⟨hqface, hj⟩))
    let other := ⋃ j : {j : I // j ≠ i}, (face j).carrier
    have hclosed : IsClosed other :=
      isClosed_iUnion_of_finite (fun j => (face j).isClosed_carrier)
    have hqother : q ∉ other := by
      intro hq
      obtain ⟨j, hj⟩ := mem_iUnion.mp hq
      exact hother j.1 j.2 hj
    refine ⟨subset_closure (mem_iUnion.mpr ⟨i, hqface⟩), ?_⟩
    intro hinside
    have hnhds : (⋃ j, (face j).carrier) ∩ otherᶜ ∈ 𝓝 q :=
      inter_mem (mem_interior_iff_mem_nhds.mp hinside) (hclosed.isOpen_compl.mem_nhds hqother)
    have hface : (face i).carrier ∈ 𝓝 q := mem_of_superset hnhds (by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx.1
      by_cases hji : j = i
      · simpa only [hji] using hj
      · exact False.elim (hx.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)))
    exact hqfront.2 (mem_interior_iff_mem_nhds.mpr hface)
  rintro q ⟨t, ht, rfl⟩
  have hcontinuous := (((face i).boundary k).smooth.continuousOn t ht).mono
    (show Ioo (0 : ℝ) 1 ⊆ Icc 0 1 from Ioo_subset_Icc_self)
  have htclosure : t ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ht
  have h := hcontinuous.mem_closure htclosure (fun _ hu => hopen hu)
  simpa only [isClosed_frontier.closure_eq] using h

end PoincareMT
