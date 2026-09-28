import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeDualDisks
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDualRegion
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBlocks
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFrontierEdgeCofaces
import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeChartWitnesses
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFaceInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)





theorem edge_region_ball (p : (T.marked 2).vertices)
    {s : Finset (T.index → ℝ × V3)} (hps : (p : T.index → ℝ × V3) ∈ s)
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2) :
    IsFinitePLBallPair (ℝ × ℝ) (T.dualRegion s) (T.dualRegionRim s) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  let N := T.ambient.barycentricDualBlock s
  let Q := (N.link (s.centroid ℝ id)).space
  let H := T.chart (T.chart_index p)
  have hpair : IsFinitePLBallPair (ℝ × ℝ) N.space Q :=
    T.isFinitePLBallPair_edge_dualBlock hs hscard
  have hQN : Q ⊆ N.space := hpair.1
  have hNK : N.space ⊆ T.ambient.space :=
    (SimplicialComplex.space_subset_of_le (T.ambient.barycentricDualBlock_le s)).trans
      T.ambient.barycentricSubdivision_isSubdivision.space_eq.subset
  have hNvertex : N.space ⊆ (T.vertexBlock p).space :=
    SimplicialComplex.space_subset_of_le (T.ambient.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hps))
  have hNS : MapsTo (fun x => (T.inverse x : X)) N.space H.source :=
    fun _ hx => (T.vertexBlock_centered_chart p).2.2.2.1 (hNvertex hx)
  by_cases hsB : s ∈ (T.marked 1).faces
  · let L := (T.marked 1).barycentricDualBlock s
    have hpB : (T.inverse p : X) ∈ frontier R :=
      (T.inverse_mem_boundary_iff (T.ambient.subset_space (T.marked_le 2 hs) hps)).mpr
        ((T.marked 1).subset_space hsB hps)
    have hsstar : s ∈ (T.ambient.closedStar p).faces := by
      refine ⟨T.marked_le 2 hs, ?_⟩
      simpa only [Finset.insert_eq_of_mem hps] using (T.marked_le 2 hs)
    have hpH : (T.inverse p : X) ∈ H.source :=
      T.star_source p ((T.ambient.closedStar p).subset_space hsstar hps)
    have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
      rcases T.chart_model (T.chart_index p) with ⟨hinside, _⟩ | ⟨hhalf, _⟩
      · exact False.elim (hpB.2 (hinside hpH))
      · exact hhalf
    let ell : C3 →L[ℝ] ℝ :=
      { toFun := fun z => z.1.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := by fun_prop }
    have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
      intro he
      have h := congrArg (fun m : C3 →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
      change (1 : ℝ) = 0 at h
      exact one_ne_zero h
    have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
    obtain ⟨t, ht, v, hv, hst, hsv, htc, hvc, htv, hW, hWlink⟩ :=
      T.exists_frontier_edge_dual_interval hs hsB hscard
    have hne : t.centroid ℝ id ≠ v.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : (T.marked 1).faces) = ⟨v, hv⟩ :=
        (T.marked 1).faceCentroid_injective he
      exact htv (congrArg Subtype.val heq)
    have hNB : N.space ∩ (T.marked 1).space = L.space :=
      T.ambient.barycentricDualBlock_space_inter_subcomplex (T.marked 1) (T.marked_le 1) s
    have hzero : N.space ∩ {x | ell (H (T.inverse x)) = 0} = L.space := by
      calc
        N.space ∩ {x | ell (H (T.inverse x)) = 0} = N.space ∩ (T.marked 1).space := by
          ext x
          exact and_congr_right (fun hx => (hfront.apply_mem_iff (hNS hx)).trans
            (T.inverse_mem_boundary_iff (hNK hx)))
        _ = L.space := hNB
    have hlink : (L.link (s.centroid ℝ id)).space = L.space ∩ Q :=
      SimplicialComplex.link_space_eq_inter_of_closedStar_eq N L
        (T.ambient.barycentricDualBlock_mono_of_subcomplex (T.marked 1) (T.marked_le 1) s)
        (s.centroid ℝ id) ((T.marked 1).barycentricDualBlock_closedStar_faceCentroid hsB)
    have hqzero : Q ∩ {x | ell (H (T.inverse x)) = 0} =
        {t.centroid ℝ id, v.centroid ℝ id} := by
      calc
        Q ∩ {x | ell (H (T.inverse x)) = 0} = L.space ∩ Q := by
          ext x
          exact ⟨fun hx => ⟨hzero.subset ⟨hQN hx.1, hx.2⟩, hx.1⟩,
            fun hx => ⟨hx.2, (hzero.symm.subset hx.1).2⟩⟩
        _ = {t.centroid ℝ id, v.centroid ℝ id} := hlink.symm.trans hWlink
    have htz : ∀ x ∈ t, ell (H (T.inverse x)) = 0 := by
      intro x hx
      have htstar : t ∈ (T.ambient.closedStar p).faces := by
        refine ⟨T.marked_le 1 ht, ?_⟩
        simpa only [Finset.insert_eq_of_mem (hst hps)] using (T.marked_le 1 ht)
      have hxH := T.star_source p ((T.ambient.closedStar p).subset_space htstar hx)
      exact (hfront.apply_mem_iff hxH).mpr
        ((T.inverse_mem_boundary_iff (T.ambient.subset_space (T.marked_le 1 ht) hx)).mpr
          ((T.marked 1).subset_space ht hx))
    obtain ⟨u, _, w, _, _, _, _, _, huQ, hwQ, hun, hwp⟩ :=
      T.exists_edge_chart_sign_witnesses p hps hs hscard (T.marked_le 1 ht) htc hst
        ell.toContinuousAffineMap.toAffineMap hell htz
    have hgc : ContinuousOn (fun x => (T.inverse x : X)) N.space :=
      continuous_subtype_val.comp_continuousOn (T.inverse_continuous.mono hNK)
    have hcuts := hpair.signed_halves_of_zero_arc (fun x => ell (H (T.inverse x)))
      (ell.continuous.comp_continuousOn (H.continuousOn.comp hgc hNS))
      hW hne hzero hqzero ⟨u.centroid ℝ id, huQ, hun⟩ ⟨w.centroid ℝ id, hwQ, hwp⟩
    have hcarrier : N.space ∩ {x | 0 ≤ ell (H (T.inverse x))} = T.dualRegion s := by
      ext x
      exact and_congr_right (fun hx => (hhalf _ (hNS hx)).symm.trans
        (T.inverse_mem_region_iff (hNK hx)))
    have hrim : L.space ∪ (Q ∩ {x | 0 ≤ ell (H (T.inverse x))}) =
        T.dualRegionRim s := by
      change L.space ∪ (Q ∩ {x | 0 ≤ ell (H (T.inverse x))}) =
        (Q ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space)
      rw [hNB]
      have hR (x : T.index → ℝ × V3) (hx : x ∈ Q) :
          0 ≤ ell (H (T.inverse x)) ↔ x ∈ (T.marked 0).space :=
        (hhalf _ (hNS (hQN hx))).symm.trans (T.inverse_mem_region_iff (hNK (hQN hx)))
      ext x
      constructor
      · rintro (hx | hx)
        · exact Or.inr hx
        · exact Or.inl ⟨hx.1, (hR x hx.1).mp hx.2⟩
      · rintro (hx | hx)
        · exact Or.inr ⟨hx.1, (hR x hx.1).mpr hx.2⟩
        · exact Or.inl hx
    rw [hcarrier, hrim] at hcuts
    exact hcuts.2
  · have hNint := T.dualBlock_mapsTo_original_interior hs hsB
    have hNR : N.space ⊆ (T.marked 0).space :=
      fun _ hx => (T.inverse_mem_region_iff (hNK hx)).mp (interior_subset (hNint hx))
    have hQR : Q ⊆ (T.marked 0).space := hQN.trans hNR
    have hNB : N.space ∩ (T.marked 1).space = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ((T.inverse_mem_boundary_iff (hNK hx.1)).mpr hx.2).2 (hNint hx.1)
    have hcarrier : T.dualRegion s = N.space := inter_eq_left.mpr hNR
    have hrim : T.dualRegionRim s = Q := by
      change (Q ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space) = Q
      rw [inter_eq_left.mpr hQR, hNB, union_empty]
    rw [hcarrier, hrim]
    exact hpair

end PoincareConjecture.M76.OriginalProperDiskTriangulation
