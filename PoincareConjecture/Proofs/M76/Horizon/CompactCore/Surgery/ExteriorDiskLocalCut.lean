import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.OriginalDiskCutCollars
import PoincareConjecture.Proofs.M76.Wall.OppositePLDomain
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLHalfspaceNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem PLDomain.exists_compact_exterior_disk_cut_with_collars
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
      frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ) ∧
      ∃ P : OriginalDiskProduct e L j,
        MapsTo P.map (D ×ˢ I) (interior H ∩ U) ∧
        IsOpen ((Subtype.val : L → X) ⁻¹' P.openStrip) ∧
        PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
        interior P.cutCarrier = interior L \ P.closedStrip ∧
        frontier P.cutCarrier = (frontier L \ P.openStrip) ∪ P.endDisks ∧
        P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
        P.closedStrip ∪ P.cutCarrier = L ∧ (interior P.cutCarrier).Nonempty ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : L → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier L → X) ⁻¹'
          (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  let := ChartedSpace.ofChartCover e he.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  have hjcompact : IsCompact (j '' D) :=
    (isCompact_closedBall (0 : V2) 1).image_of_continuousOn hj.continuousOn
  obtain ⟨H, hH, hcore, _, hcharts⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      (hK.union hjcompact) isOpen_univ (subset_univ _)
  have hPH : PLDomain e H := ⟨he.cover, he.compatible, hH.isClosed, hcharts⟩
  obtain ⟨hext, hextfront⟩ := he.compl_interior
  have hfrontH : frontier (interior K)ᶜ ⊆ interior H := by
    rw [hextfront]
    exact he.closed.frontier_subset.trans (fun _ hx => hcore (Or.inl hx))
  let L := H ∩ (interior K)ᶜ
  have hL : IsCompact L := hH.inter_right hext.closed
  have hPL : PLDomain e L := hPH.inter_of_frontier_subset_interior hext hfrontH
  have hLfront : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ) := by
    rw [Set.frontier_inter_of_frontier_subset_interior hPH.closed hext.closed hfrontH,
      hextfront]
  have hjH (z : D) : j z ∈ interior H := hcore (Or.inr ⟨z, z.property, rfl⟩)
  have hjL : MapsTo j D L := fun z hz => ⟨interior_subset (hjH ⟨z, hz⟩), hjext hz⟩
  have hjproper : ∀ z : D, j z ∈ frontier L ↔ (z : V2) ∈ Q := by
    intro z
    rw [hLfront]
    constructor
    · rintro (hz | hz)
      · exact (hproper z).mp hz
      · exact False.elim (hz.1.2 (hjH z))
    · exact fun hz => Or.inl ((hproper z).mpr hz)
  obtain ⟨P, hsmall, hopen, hcutPL, hcutcompact, hint, hfront, hoverlap, hcover, hne, hcollars⟩ :=
    exists_original_disk_cut_domain_with_collars hL hPL hj hemb hjL hjproper
      (isOpen_interior.inter hU) (by
        rintro x ⟨z, hz, rfl⟩
        exact ⟨hjH ⟨z, hz⟩, hjU ⟨z, hz, rfl⟩⟩)
  exact ⟨H, L, hH, hPH, hcore, rfl, hL, hPL, hLfront,
    P, hsmall, hopen, hcutPL, hcutcompact, hint, hfront, hoverlap, hcover, hne, hcollars⟩

theorem PLDomain.exists_compact_exterior_disk_cut
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
      frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ) ∧
      ∃ P : OriginalDiskProduct e L j,
        MapsTo P.map (D ×ˢ I) (interior H ∩ U) ∧
        IsOpen ((Subtype.val : L → X) ⁻¹' P.openStrip) ∧
        PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
        interior P.cutCarrier = interior L \ P.closedStrip ∧
        frontier P.cutCarrier = (frontier L \ P.openStrip) ∪ P.endDisks ∧
        P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
        P.closedStrip ∪ P.cutCarrier = L ∧ (interior P.cutCarrier).Nonempty := by
  obtain ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, hLfront, P, hsmall, hopen, hcutPL, hcutcompact, hint, hfront, hoverlap, hcover, hne, _⟩ :=
    PLDomain.exists_compact_exterior_disk_cut_with_collars he hK hj hemb hjext hproper hU hjU
  exact ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, hLfront, P, hsmall, hopen, hcutPL, hcutcompact, hint, hfront, hoverlap, hcover, hne⟩

end PoincareConjecture.M76
