import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Surgery.ExteriorDiskAttachment
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalDiskStripDomain

/-!
# A common closed cut for an original exterior disk

The original disk constructs one strip in a compact exterior neighborhood.
The core, whole strip, and remaining exterior are compact PL domains. Their
literal intersections give the retained old boundary, lateral band, and two
caps. Both old and compressed regions are unions of these same three pieces.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_original_exterior_disk_common_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K U : Set X} {j : V2 → X}
    (he : PLDomain e K) (hK : IsCompact K)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hjext : MapsTo j D (interior K)ᶜ)
    (hproper : ∀ z : D, j z ∈ frontier K ↔ (z : V2) ∈ Q)
    (hU : IsOpen U) (hjU : j '' D ⊆ U) :
    ∃ H L : Set X,
      IsCompact H ∧ PLDomain e H ∧ K ∪ j '' D ⊆ interior H ∧
      L = H ∩ (interior K)ᶜ ∧ IsCompact L ∧ PLDomain e L ∧
      ∃ P : OriginalDiskProduct e L j,
        MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) (interior H ∩ U) ∧
        IsCompact P.closedStrip ∧ PLDomain e P.closedStrip ∧
        IsCompact P.cutCarrier ∧ PLDomain e P.cutCarrier ∧
        IsCompact (K ∪ P.closedStrip) ∧ PLDomain e (K ∪ P.closedStrip) ∧
        K ∪ L = H ∧ P.closedStrip ∪ P.cutCarrier = L ∧
        (K ∪ P.closedStrip) ∪ P.cutCarrier = H ∧
        K ∩ P.cutCarrier = frontier K \ P.openStrip ∧
        P.closedStrip ∩ K = P.map '' (Q ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) ∧
        P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
        (K ∪ P.closedStrip) ∩ P.cutCarrier =
          (frontier K \ P.openStrip) ∪ P.endDisks ∧
        frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks ∧
        frontier P.closedStrip =
          (P.map '' (Q ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2))) ∪ P.endDisks ∧
        frontier P.cutCarrier =
          ((frontier K ∪ (frontier H ∩ (interior K)ᶜ)) \ P.openStrip) ∪ P.endDisks ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          IsOpen ((Subtype.val : L → X) ⁻¹'
            (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier L → X) ⁻¹'
            (P.map '' (Q ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier K → X) ⁻¹'
            (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, hLfront,
      P, hsmall, hopen, hcutPL, hcutcompact, hint, hcutfront, hoverlap,
      hcover, _, hcollars⟩ :=
    he.exists_compact_exterior_disk_cut_with_collars hK hj hemb hjext hproper hU hjU
  have hKH : K ⊆ interior H := fun _ hx => hcore (Or.inl hx)
  have hstripH : P.closedStrip ⊆ interior H := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsmall ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩).1
  obtain ⟨hattachPL, hattachcompact, _, _, hattachfront, hcollars'⟩ :=
    P.exterior_attachment_geometry_with_collars he hK hKH hLE hLfront hstripH
      hcutPL hint hcutfront hoverlap hcollars
  have hKL : K ∪ L = H := by
    rw [hLE]
    ext x
    constructor
    · rintro (hx | hx)
      · exact interior_subset (hKH hx)
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, fun hi => hxK (interior_subset hi)⟩
  have hKcut : K ∩ P.cutCarrier = frontier K \ P.openStrip := by
    change K ∩ (L \ P.openStrip) = _
    simp only [hLE, frontier, he.closed.closure_eq]
    ext x
    constructor
    · exact fun hx => ⟨⟨hx.1, hx.2.1.2⟩, hx.2.2⟩
    · exact fun hx => ⟨hx.1.1, ⟨⟨interior_subset (hKH hx.1.1), hx.1.2⟩, hx.2⟩⟩
  have hstripK : P.closedStrip ∩ K = P.closedStrip ∩ frontier L := by
    rw [hLfront]
    ext x
    constructor
    · rintro ⟨hxstrip, hxK⟩
      have hxL : x ∈ H ∩ (interior K)ᶜ := hLE ▸ P.closedStrip_subset hxstrip
      exact ⟨hxstrip, Or.inl ⟨subset_closure hxK, hxL.2⟩⟩
    · rintro ⟨hxstrip, hxfront | hxfront⟩
      · exact ⟨hxstrip, he.closed.frontier_subset hxfront⟩
      · exact False.elim (hxfront.1.2 (hstripH hxstrip))
  refine ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, hsmall,
    P.isCompact_closed_strip (by norm_num), P.plDomain_closedStrip hL hPL hopen,
    hcutcompact, hcutPL, hattachcompact, hattachPL, hKL, hcover, ?_, hKcut,
    hstripK.trans P.closedStrip_inter_frontier, hoverlap, ?_, hattachfront,
    P.frontier_closedStrip, ?_, hcollars'⟩
  · rw [union_assoc, hcover, hKL]
  · rw [union_inter_distrib_right, hKcut, hoverlap]
  · rw [hcutfront, hLfront]

end PoincareMT.M76
