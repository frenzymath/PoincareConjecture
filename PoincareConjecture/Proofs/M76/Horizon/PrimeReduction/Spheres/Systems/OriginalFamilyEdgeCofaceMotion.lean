import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalFamilyEdgePosition

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_sphere_system_edge_coface_motion
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {Z : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K M : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hMK : M ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (p q : E) (hpq : p ≠ q) (hpqK : ({p, q} : Finset E) ∈ K.faces)
    (hpqM : ({p, q} : Finset E) ∉ M.faces) :
    ∃ (G : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ Disjoint C (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 → a ≠ {p, q} →
        Disjoint C (g '' convexHull ℝ (a : Set E))) ∧
      EqOn G id Cᶜ ∧
      (∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (G '' S i)) ∧
      ((G '' (⋃ i, S i)) ∩ (g '' segment ℝ p q)).Finite ∧
      HasOriginalEdgeCofaceCharts e (G '' (⋃ i, S i)) K g {p, q} := by
  classical
  obtain ⟨B, hB, hsource, hne, hparameter, hphysical, hcofaces⟩ :=
    K.exists_original_edge_coordinates_with_cofaces g hgi e hstars p q hpq hpqK
  obtain ⟨U, hU, haxis, hUZ, hUV, hUE⟩ :=
    K.exists_original_edge_open_protection M hK hMK g hgc hgi Z hZ hmark p q hpq hpqK hpqM
  have hpB := hsource (left_mem_segment ℝ p q)
  have hqB := hsource (right_mem_segment ℝ p q)
  have hpv : g p ∈ g '' K.vertices :=
    mem_image_of_mem g (K.face_subset_vertices hpqK (Finset.mem_insert_self _ _))
  have hqv : g q ∈ g '' K.vertices :=
    mem_image_of_mem g (K.face_subset_vertices hpqK (by simp))
  have hpS : B.symm (B (g p)) ∉ (⋃ i, S i) := by
    rw [B.left_inv hpB]
    exact fun hs => disjoint_left.mp hSV hs hpv
  have hqS : B.symm (B (g q)) ∉ (⋃ i, S i) := by
    rw [B.left_inv hqB]
    exact fun hs => disjoint_left.mp hSV hs hqv
  have haxisB (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      B.symm (AffineMap.lineMap (B (g p)) (B (g q)) t) ∈ U := by
    rw [(hparameter t ⟨ht.1.le, ht.2.le⟩).2]
    exact haxis (lineMap_mem_openSegment ℝ p q ht)
  obtain ⟨G, C, hC, hCU, hG, hGPL, hGinv, hSphere, hfinite, hcharts⟩ :=
    exists_sphere_system_whole_edge_position S sS hdis hcover he B hB hU (B (g p)) (B (g q)) hne
      (fun t ht => (hparameter t ht).1) hpS hqS haxisB
  have hsegmentB : segment ℝ (B (g p)) (B (g q)) ⊆ B.target := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨t, ht, rfl⟩
    exact (hparameter t ht).1
  have hphysical_mem (x : V3) (hx : x ∈ B.target) :
      B.symm x ∈ g '' segment ℝ p q ↔ x ∈ segment ℝ (B (g p)) (B (g q)) := by
    rw [← hphysical]
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (B.symm.injOn (hsegmentB hy) hx heq) ▸ hy
    · intro hxseg
      exact mem_image_of_mem B.symm hxseg
  refine ⟨G, C, hC, hUZ.mono_left hCU, hUV.mono_left hCU,
    (fun a ha hc hne => (hUE a ha hc hne).mono_left hCU),
    hG, hGPL, hGinv, hSphere, ?_, ?_⟩
  · simpa only [hphysical] using hfinite
  · intro y hy
    simp only [Finset.coe_pair, convexHull_pair] at hy
    obtain ⟨x, hxe, hxy⟩ := hphysical.symm.subset hy.2
    have hxS : B.symm x ∈ G '' (⋃ i, S i) := hxy.symm ▸ hy.1
    obtain ⟨V, F, hV, hxV, hVB, hF, hFS, hFL⟩ := hcharts x hxe hxS
    have hyB : y ∈ B.source := hxy ▸ B.map_target (hsegmentB hxe)
    have hBy : B y = x := by rw [← hxy, B.right_inv (hsegmentB hxe)]
    refine ⟨B, V, F, hB, hyB, hV, hBy.symm ▸ hxV, hVB,
      hF.trans hBy.symm, hFS, ?_, hcofaces⟩
    intro z hz
    simpa only [Finset.coe_pair, convexHull_pair] using
      (hphysical_mem (F z) (hVB hz)).trans (hFL z hz)

end PoincareConjecture.M76
