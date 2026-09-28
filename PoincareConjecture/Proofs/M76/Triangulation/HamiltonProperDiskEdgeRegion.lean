import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeRims
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeWitnesses
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

theorem HamiltonProperDiskTriangulation.edge_region_ball
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    (p : T.disk.vertices) {s : Finset E} (hps : (p : E) ∈ s)
    (hs : s ∈ T.disk.faces) (hcard : s.card = 2) :
    IsFinitePLBallPair (ℝ × ℝ) (T.dualRegion s) (T.dualRegionRim s) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let N := T.ambient.barycentricDualBlock s
  let Q := (N.link (s.centroid ℝ id)).space
  let H := (T.pairChart p).chart
  have hpD : (p : E) ∈ D := T.disk_space.subset
    (T.disk.vertices_subset_space p.property)
  have hpair : IsFinitePLBallPair (ℝ × ℝ) N.space Q :=
    T.ambient.isFinitePLBallPair_barycentricDualBlock_of_interior_edge h3
      (T.disk_le hs) hcard ⟨p, subset_convexHull ℝ _ hps,
        T.region_interior (T.disk_subset_region hpD)⟩
  have hQN : Q ⊆ N.space := hpair.1
  have hNS : N.space ⊆ H.source :=
    (SimplicialComplex.space_subset_of_le
      (T.ambient.barycentricDualBlock_antitone
        (Finset.singleton_subset_iff.mpr hps))).trans
      (T.vertexBlock_centered_chart p).2.2.2.1
  by_cases hsF : s ∈ T.boundary.faces
  · let L := T.boundary.barycentricDualBlock s
    have hpF : (p : E) ∈ frontier R := T.boundary_space.subset
      (T.boundary.subset_space hsF hps)
    have hpH : (p : E) ∈ H.source := T.star_source p
      ((T.ambient.closedStar p).subset_space
        ⟨T.disk_le hs, by simpa only [Finset.insert_eq_of_mem hps] using T.disk_le hs⟩ hps)
    have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
      rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hhalf, _⟩
      · exact False.elim (hpF.2 (hinside hpH))
      · exact hhalf
    let ell : V →L[ℝ] ℝ :=
      { toFun := fun z => z.1.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := by fun_prop }
    have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
      intro he
      have h := congrArg (fun m : V →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
      change (1 : ℝ) = 0 at h
      exact one_ne_zero h
    have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
    obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces⟩ :=
      T.exists_frontier_edge_triangle_cofaces hs hsF hcard
    have hbound : ∀ v ∈ T.boundary.faces, v.card ≤ 2 + 1 :=
      fun _ hv => T.frontier_face_card_le h3 hv
    have hW := T.boundary.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
      hbound hsF ht hu hcard htc huc hst hsu htu hcofaces
    have hWlink := T.boundary.barycentricDualBlock_link_space_of_paired_facet
      hbound hsF ht hu hcard htc huc hst hsu hcofaces
    have hne : t.centroid ℝ id ≠ u.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : T.boundary.faces) = ⟨u, hu⟩ :=
        T.boundary.faceCentroid_injective he
      exact htu (congrArg Subtype.val heq)
    have hNF : N.space ∩ frontier R = L.space := by
      simpa only [T.boundary_space] using
        T.ambient.barycentricDualBlock_space_inter_subcomplex T.boundary T.boundary_le s
    have hzero : N.space ∩ {x | ell (H x) = 0} = L.space := by
      calc
        N.space ∩ {x | ell (H x) = 0} = N.space ∩ frontier R := by
          ext x
          exact and_congr_right (fun hx => hfront.apply_mem_iff (hNS hx))
        _ = L.space := hNF
    have hlink : (L.link (s.centroid ℝ id)).space = L.space ∩ Q :=
      SimplicialComplex.link_space_eq_inter_of_closedStar_eq N L
        (T.ambient.barycentricDualBlock_mono_of_subcomplex T.boundary T.boundary_le s)
        (s.centroid ℝ id) (T.boundary.barycentricDualBlock_closedStar_faceCentroid hsF)
    have hqzero : Q ∩ {x | ell (H x) = 0} = {t.centroid ℝ id, u.centroid ℝ id} := by
      calc
        Q ∩ {x | ell (H x) = 0} = L.space ∩ Q := by
          ext x
          constructor
          · exact fun hx => ⟨hzero.subset ⟨hQN hx.1, hx.2⟩, hx.1⟩
          · exact fun hx => ⟨hx.2, (hzero.symm.subset hx.1).2⟩
        _ = {t.centroid ℝ id, u.centroid ℝ id} := hlink.symm.trans hWlink
    have hRclosed : IsClosed R := T.region_space ▸
      (T.region.isCompact_space_of_finite (T.finite.subset T.region_le)).isClosed
    have hFR : frontier R ⊆ R := fun _ hx => hRclosed.closure_eq.subset hx.1
    have hmeet : (convexHull ℝ (t : Set E) ∩ interior T.ambient.space).Nonempty := by
      have hnonempty : (convexHull ℝ (t : Set E)).Nonempty :=
        (Finset.coe_nonempty.mpr (T.boundary.nonempty_of_mem_faces ht)).convexHull
      obtain ⟨x, hx⟩ := hnonempty
      exact ⟨x, hx, T.region_interior (hFR (T.boundary_space.subset
        (T.boundary.convexHull_subset_space ht hx)))⟩
    have htz : ∀ x ∈ t, ell (H x) = 0 := by
      intro x hx
      have htstar : t ∈ (T.ambient.closedStar p).faces :=
        ⟨T.boundary_le ht, by
          simpa only [Finset.insert_eq_of_mem (hst hps)] using (T.boundary_le ht)⟩
      have hxH := T.star_source p ((T.ambient.closedStar p).subset_space htstar hx)
      exact (hfront.apply_mem_iff hxH).mpr
        (T.boundary_space.subset (T.boundary.subset_space ht hx))
    obtain ⟨v, _, w, _, _, _, _, _, hvQ, hwQ, hvn, hwp⟩ :=
      T.exists_edge_chart_sign_witnesses h3 p hps hs hcard (T.boundary_le ht) htc hst
        hmeet ell.toContinuousAffineMap.toAffineMap hell htz
    have hcuts := hpair.signed_halves_of_zero_arc (fun x => ell (H x))
      (ell.continuous.comp_continuousOn (H.continuousOn.mono hNS)) hW.1 hne hzero hqzero
      ⟨v.centroid ℝ id, hvQ, hvn⟩ ⟨w.centroid ℝ id, hwQ, hwp⟩
    have hcarrier : N.space ∩ {x | 0 ≤ ell (H x)} = T.dualRegion s := by
      ext x
      exact and_congr_right (fun hx => (hhalf x (hNS hx)).symm)
    have hrim : L.space ∪ (Q ∩ {x | 0 ≤ ell (H x)}) = T.dualRegionRim s := by
      change L.space ∪ (Q ∩ {x | 0 ≤ ell (H x)}) =
        (Q ∩ R) ∪ (N.space ∩ frontier R)
      rw [hNF]
      ext x
      constructor
      · rintro (hx | hx)
        · exact Or.inr hx
        · exact Or.inl ⟨hx.1, (hhalf x (hNS (hQN hx.1))).mpr hx.2⟩
      · rintro (hx | hx)
        · exact Or.inr ⟨hx.1, (hhalf x (hNS (hQN hx.1))).mp hx.2⟩
        · exact Or.inl hx
    rw [hcarrier, hrim] at hcuts
    exact hcuts.2
  · have hNint := T.dualBlock_subset_interior hs hsF
    have hNR : N.space ⊆ R := hNint.trans interior_subset
    have hQR : Q ⊆ R := hQN.trans hNR
    have hNF : N.space ∩ frontier R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2.2 (hNint hx.1)
    have hcarrier : T.dualRegion s = N.space := inter_eq_left.mpr hNR
    have hrim : T.dualRegionRim s = Q := by
      change (Q ∩ R) ∪ (N.space ∩ frontier R) = Q
      rw [inter_eq_left.mpr hQR, hNF, union_empty]
    rw [hcarrier, hrim]
    exact hpair

end PoincareConjecture.M76.HamiltonIndexOne
