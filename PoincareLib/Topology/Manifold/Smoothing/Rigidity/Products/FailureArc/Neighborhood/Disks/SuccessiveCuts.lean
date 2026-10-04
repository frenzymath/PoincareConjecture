import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalDiskCutDomainConstruction

/-! # Successive disjoint original-atlas cuts along two proper disks -/

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareMT.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_successive_disjoint_original_disk_cuts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j₀ j₁ : V2 → X}
    (hQ : IsCompact Q) (he : PLDomain e Q)
    (hj₀ : PolyhedralPLInCharts e j₀ Disk) (hj₁ : PolyhedralPLInCharts e j₁ Disk)
    (hi₀ : IsEmbedding (fun z : Disk => j₀ z)) (hi₁ : IsEmbedding (fun z : Disk => j₁ z))
    (hQ₀ : MapsTo j₀ Disk Q) (hQ₁ : MapsTo j₁ Disk Q)
    (hp₀ : ∀ z : Disk, j₀ z ∈ frontier Q ↔ (z : V2) ∈ Rim)
    (hp₁ : ∀ z : Disk, j₁ z ∈ frontier Q ↔ (z : V2) ∈ Rim)
    (hdis : Disjoint (j₀ '' Disk) (j₁ '' Disk)) :
    ∃ (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e P₀.cutCarrier j₁),
      PLDomain e P₀.cutCarrier ∧ IsCompact P₀.cutCarrier ∧
      PLDomain e P₁.cutCarrier ∧ IsCompact P₁.cutCarrier ∧
      Disjoint P₀.closedStrip P₁.closedStrip ∧
      Disjoint P₀.closedStrip (j₁ '' Disk) ∧
      MapsTo j₁ Disk P₀.cutCarrier ∧
      (∀ z : Disk, j₁ z ∈ frontier P₀.cutCarrier ↔ (z : V2) ∈ Rim) ∧
      interior P₀.cutCarrier = interior Q \ P₀.closedStrip ∧
      frontier P₀.cutCarrier = (frontier Q \ P₀.openStrip) ∪ P₀.endDisks ∧
      P₀.closedStrip ∩ P₀.cutCarrier = P₀.endDisks ∧
      P₀.closedStrip ∪ P₀.cutCarrier = Q ∧
      interior P₁.cutCarrier = interior P₀.cutCarrier \ P₁.closedStrip ∧
      frontier P₁.cutCarrier = (frontier P₀.cutCarrier \ P₁.openStrip) ∪ P₁.endDisks ∧
      P₁.closedStrip ∩ P₁.cutCarrier = P₁.endDisks ∧
      P₁.closedStrip ∪ P₁.cutCarrier = P₀.cutCarrier ∧
      (interior P₁.cutCarrier).Nonempty := by
  have hj₁compact : IsCompact (j₁ '' Disk) :=
    (isCompact_closedBall _ _).image_of_continuousOn hj₁.continuousOn
  obtain ⟨P₀, hsmall₀, _, hPL₀, hcompact₀, hinterior₀, hfront₀, hoverlap₀, hcover₀, _⟩ :=
    exists_original_disk_cut_domain hQ he hj₀ hi₀ hQ₀ hp₀ hj₁compact.isClosed.isOpen_compl
      (fun x hx => fun hy => Set.disjoint_left.mp hdis hx hy)
  have hhalf : Disk ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2) ⊆ Disk ×ˢ I := by
    intro z hz
    exact ⟨hz.1, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hstrip₀ : Disjoint P₀.closedStrip (j₁ '' Disk) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact hsmall₀ (hhalf hz) hx
  have hopen₀ : P₀.openStrip ⊆ P₀.closedStrip :=
    image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hend₀ : P₀.endDisks ⊆ P₀.closedStrip := by
    rw [← P₀.closedStrip_sdiff_openStrip]
    exact sdiff_subset
  have havoid (z : Disk) : j₁ z ∉ P₀.closedStrip :=
    fun hz => Set.disjoint_left.mp hstrip₀ hz (mem_image_of_mem j₁ z.property)
  have hQ₁cut : MapsTo j₁ Disk P₀.cutCarrier := by
    intro z hz
    exact ⟨hQ₁ hz, fun ho => havoid ⟨z, hz⟩ (hopen₀ ho)⟩
  have hp₁cut (z : Disk) : j₁ z ∈ frontier P₀.cutCarrier ↔ (z : V2) ∈ Rim := by
    rw [hfront₀]
    constructor
    · rintro (h | h)
      · exact (hp₁ z).mp h.1
      · exact (havoid z (hend₀ h)).elim
    · intro hz
      exact Or.inl ⟨(hp₁ z).mpr hz, fun ho => havoid z (hopen₀ ho)⟩
  have hstrip₀closed : IsClosed P₀.closedStrip :=
    (P₀.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  obtain ⟨P₁, hsmall₁, _, hPL₁, hcompact₁, hinterior₁, hfront₁, hoverlap₁, hcover₁, hne₁⟩ :=
    exists_original_disk_cut_domain hcompact₀ hPL₀ hj₁ hi₁ hQ₁cut hp₁cut
      hstrip₀closed.isOpen_compl (by
        rintro _ ⟨z, hz, rfl⟩
        exact havoid ⟨z, hz⟩)
  have hstrips : Disjoint P₀.closedStrip P₁.closedStrip := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨z, hz, rfl⟩
    exact hsmall₁ (hhalf hz) hx
  exact ⟨P₀, P₁, hPL₀, hcompact₀, hPL₁, hcompact₁, hstrips, hstrip₀,
    hQ₁cut, hp₁cut, hinterior₀, hfront₀, hoverlap₀, hcover₀,
    hinterior₁, hfront₁, hoverlap₁, hcover₁, hne₁⟩

end PoincareMT.M76.Dehn.Annuli
