import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.EdgeAmbient
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.EdgeBase
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut



set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem edge_region_ball (p : (T.marked 2).vertices) {s : Finset E}
    (hps : (p : E) ∈ s) (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2) :
    IsFinitePLBallPair P2 (T.dualRegion s) (T.dualRegionRim s) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  let N := T.ambient.barycentricDualBlock s
  let Q := (N.link (s.centroid ℝ id)).space
  have hpair : IsFinitePLBallPair P2 N.space Q := T.isFinitePLBallPair_edge_dualBlock hs hscard
  have hQN : Q ⊆ N.space := hpair.1
  have hNS : N.space ⊆ (T.ambient.closedStar p).space := T.dualBlock_subset_star p hps
  by_cases hsB : s ∈ (T.marked 1).faces
  · let L := (T.marked 1).barycentricDualBlock s
    have hmodel := T.boundary_chart_model p ((T.marked 1).subset_space hsB hps)
    let ell : C3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ)
    have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
      intro he
      have h := congrArg (fun m : C3 →ₗ[ℝ] ℝ ↦ m ((1, 0), 0)) he
      change (1 : ℝ) = 0 at h
      exact one_ne_zero h
    obtain ⟨t, ht, v, hv, hst, hsv, htc, hvc, htv, hW, hWlink⟩ :=
      T.exists_boundary_edge_dual_interval hs hsB hscard
    have hne : t.centroid ℝ id ≠ v.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : (T.marked 1).faces) = ⟨v, hv⟩ :=
        (T.marked 1).faceCentroid_injective he
      exact htv (congrArg Subtype.val heq)
    have hNB : N.space ∩ (T.marked 1).space = L.space :=
      T.ambient.barycentricDualBlock_space_inter_subcomplex (T.marked 1) (T.marked_le 1) s
    have hzero : N.space ∩ {x | ell (T.chart p x) = 0} = L.space := by
      calc
        N.space ∩ {x | ell (T.chart p x) = 0} = N.space ∩ (T.marked 1).space := by
          ext x
          exact and_congr_right (fun hx ↦ (hmodel.2 x (hNS hx)).symm)
        _ = L.space := hNB
    have hlink : (L.link (s.centroid ℝ id)).space = L.space ∩ Q :=
      link_space_eq_inter_of_closedStar_eq N L
        (T.ambient.barycentricDualBlock_mono_of_subcomplex (T.marked 1) (T.marked_le 1) s)
        (s.centroid ℝ id) ((T.marked 1).barycentricDualBlock_closedStar_faceCentroid hsB)
    have hqzero : Q ∩ {x | ell (T.chart p x) = 0} =
        {t.centroid ℝ id, v.centroid ℝ id} := by
      calc
        Q ∩ {x | ell (T.chart p x) = 0} = L.space ∩ Q := by
          ext x
          exact ⟨fun hx ↦ ⟨hzero.subset ⟨hQN hx.1, hx.2⟩, hx.1⟩,
            fun hx ↦ ⟨hx.2, (hzero.symm.subset hx.1).2⟩⟩
        _ = {t.centroid ℝ id, v.centroid ℝ id} := hlink.symm.trans hWlink
    have htz : ∀ x ∈ t, ell (T.chart p x) = 0 := by
      intro x hx
      have htstar : t ∈ (T.ambient.closedStar p).faces :=
        ⟨T.marked_le 1 ht, by
          simpa only [Finset.insert_eq_of_mem (hst hps)] using T.marked_le 1 ht⟩
      exact (hmodel.2 x ((T.ambient.closedStar p).subset_space htstar hx)).mp
        ((T.marked 1).subset_space ht hx)
    obtain ⟨u, _, w, _, _, _, _, _, huQ, hwQ, hun, hwp⟩ :=
      T.exists_edge_chart_sign_witnesses p hps hs hscard (T.marked_le 1 ht) htc hst
        ell.toContinuousAffineMap.toAffineMap hell htz
    have hcont : ContinuousOn (fun x ↦ ell (T.chart p x)) N.space :=
      ell.continuous.comp_continuousOn
        (((T.star_affine p).continuousOn (finite_closedStar_faces T.finite p)).mono hNS)
    have hcuts := hpair.signed_halves_of_zero_arc (fun x ↦ ell (T.chart p x))
      hcont hW hne hzero hqzero ⟨u.centroid ℝ id, huQ, hun⟩ ⟨w.centroid ℝ id, hwQ, hwp⟩
    have hcarrier : N.space ∩ {x | 0 ≤ ell (T.chart p x)} = T.dualRegion s := by
      ext x
      exact and_congr_right (fun hx ↦ (hmodel.1 x (hNS hx)).symm)
    have hrim : L.space ∪ (Q ∩ {x | 0 ≤ ell (T.chart p x)}) = T.dualRegionRim s := by
      change L.space ∪ (Q ∩ {x | 0 ≤ ell (T.chart p x)}) =
        (Q ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space)
      rw [hNB]
      have hR (x : E) (hx : x ∈ Q) :
          0 ≤ ell (T.chart p x) ↔ x ∈ (T.marked 0).space :=
        (hmodel.1 x (hNS (hQN hx))).symm
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
  · rw [T.dualRegion_eq_dualBlock_of_not_boundary hs hsB,
      T.dualRegionRim_eq_link_of_not_boundary hs hsB]
    exact hpair

end Geometry.SimplicialComplex.CoorientedSurfaceStars
