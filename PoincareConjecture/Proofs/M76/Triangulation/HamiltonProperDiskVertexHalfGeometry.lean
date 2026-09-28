import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexHalfCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBase
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

theorem HamiltonProperDiskTriangulation.vertex_half_ballPair_and_outside
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (w : ℝ) (hw : w ≠ 0) :
    IsFinitePLBallPair V
      (T.dualRegion {(p : E)} ∩ {x | 0 ≤ w * ((T.pairChart p).chart x).2})
      ((T.dualRegionRim {(p : E)} ∩ {x | 0 ≤ w * ((T.pairChart p).chart x).2}) ∪
        T.diskVertexBlock p) ∧
      (((T.dualRegionRim {(p : E)} ∩
          {x | 0 ≤ w * ((T.pairChart p).chart x).2}) ∪ T.diskVertexBlock p) \
        T.diskVertexBlock p).Nonempty := by
  classical
  let N := T.vertexBlock p
  let Z : Set E := {x | 0 ≤ w * ((T.pairChart p).chart x).2}
  obtain ⟨hN, hpN, hstar, _, _⟩ := T.vertexBlock_centered_chart p
  obtain ⟨boundary, g, hg, hgi, hgp, hgint, hnormal, hregion, hdisk, hfront⟩ :=
    T.exists_vertex_half_chart p w hw
  let c : V ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  obtain ⟨hhalf, houter⟩ :=
    hg.conical_halfBlock_ball_pairs hN hgi hpN hstar hgp hgint c boundary
  have hlinksub : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hbase : T.diskVertexBlock p = N.space ∩ D := T.diskVertexBlock_eq_inter p
  have hbody : SimplicialComplex.chartedHalfBlock N.space g boundary =
      T.dualRegion {(p : E)} ∩ Z := by
    ext x
    change (x ∈ N.space ∧ (boundary = true → 0 ≤ (g x).1.1) ∧ 0 ≤ (g x).2) ↔
      ((x ∈ N.space ∧ x ∈ R) ∧ 0 ≤ w * ((T.pairChart p).chart x).2)
    by_cases hxN : x ∈ N.space
    · rw [← hregion x hxN, hnormal]
      tauto
    · tauto
  have hout : SimplicialComplex.chartedHalfBlockOuter (N.link p).space g boundary =
      ((N.link p).space ∩ R) ∩ Z := by
    ext x
    change (x ∈ (N.link p).space ∧
        (boundary = true → 0 ≤ (g x).1.1) ∧ 0 ≤ (g x).2) ↔
      ((x ∈ (N.link p).space ∧ x ∈ R) ∧ 0 ≤ w * ((T.pairChart p).chart x).2)
    by_cases hxL : x ∈ (N.link p).space
    · rw [← hregion x (hlinksub hxL), hnormal]
      tauto
    · tauto
  have hactive : SimplicialComplex.chartedHalfBlockActive N.space g boundary =
      ((N.space ∩ frontier R) ∩ Z) ∪ T.diskVertexBlock p := by
    ext x
    constructor
    · rintro ⟨hxN, hr, hn, hF | hD⟩
      · have hn' : x ∈ Z := by
          change 0 ≤ w * ((T.pairChart p).chart x).2
          rwa [hnormal x] at hn
        exact Or.inl ⟨⟨hxN, (hfront x hxN).mpr hF⟩, hn'⟩
      · exact Or.inr (hbase.symm.subset ⟨hxN, (hdisk x hxN).mpr ⟨hr, hD⟩⟩)
    · rintro (⟨⟨hxN, hxF⟩, hn⟩ | hxB)
      · have hxG := (hfront x hxN).mp hxF
        refine ⟨hxN, ?_, (hnormal x).symm ▸ hn, Or.inl hxG⟩
        intro _
        exact hxG.2.ge
      · obtain ⟨hxN, hxD⟩ := hbase.subset hxB
        obtain ⟨hr, hz⟩ := (hdisk x hxN).mp hxD
        exact ⟨hxN, hr, hz.ge, Or.inr hz⟩
  have hrim : SimplicialComplex.chartedHalfBlockOuter (N.link p).space g boundary ∪
      SimplicialComplex.chartedHalfBlockActive N.space g boundary =
      (T.dualRegionRim {(p : E)} ∩ Z) ∪ T.diskVertexBlock p := by
    have hq : T.dualRegionRim {(p : E)} =
        ((N.link p).space ∩ R) ∪ (N.space ∩ frontier R) := by
      simp only [HamiltonProperDiskTriangulation.dualRegionRim,
        Finset.centroid_singleton, id_eq, N,
        HamiltonProperDiskTriangulation.vertexBlock]
    rw [hout, hactive, hq]
    ext x
    simp only [mem_union, mem_inter_iff]
    tauto
  have hball : IsFinitePLBallPair V (T.dualRegion {(p : E)} ∩ Z)
      ((T.dualRegionRim {(p : E)} ∩ Z) ∪ T.diskVertexBlock p) := by
    rwa [hbody, hrim] at hhalf
  refine ⟨hball, ?_⟩
  obtain ⟨x, hx, hnot⟩ := houter.sdiff_nonempty
  refine ⟨x, hrim.subset (Or.inl hx), ?_⟩
  intro hxB
  exact hnot ⟨hx, hactive.symm.subset (Or.inr hxB)⟩

theorem HamiltonProperDiskTriangulation.vertex_half_base_complement
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (w : ℝ) (hw : w ≠ 0) :
    IsFinitePLBallPair P2
      (((T.dualRegionRim {(p : E)} ∩
          {x | 0 ≤ w * ((T.pairChart p).chart x).2}) ∪ T.diskVertexBlock p) \
        (T.diskVertexBlock p \ (T.dualRegionRim {(p : E)} ∩ D)))
      (T.dualRegionRim {(p : E)} ∩ D) := by
  obtain ⟨hhalf, hout⟩ := T.vertex_half_ballPair_and_outside p w hw
  exact hhalf.boundary_disk_complement (by simp [Module.finrank_prod])
    (T.vertex_base_ballPair p) subset_union_right hout

end PoincareConjecture.M76.HamiltonIndexOne
