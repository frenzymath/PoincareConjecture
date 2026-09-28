import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.Pair
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskCutDomainConstruction

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_unchanged_product_in_disjoint_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j₀ j₁ : V2 → X}
    (P₀ : OriginalDiskProduct e R j₀) (P₁ : OriginalDiskProduct e R j₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen₀ : IsOpen ((Subtype.val : R → X) ⁻¹' P₀.openStrip))
    (hdis : Disjoint (P₀.map '' (Disk ×ˢ I)) (P₁.map '' (Disk ×ˢ I)))
    (hopen₁ : ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : R → X) ⁻¹' (P₁.map '' (Disk ×ˢ Ioo (-v) v)))) :
    ∃ Q₁ : OriginalDiskProduct e P₀.cutCarrier j₁, Q₁.map = P₁.map ∧
      PLDomain e P₀.cutCarrier ∧ IsCompact P₀.cutCarrier ∧
      PLDomain e Q₁.cutCarrier ∧ IsCompact Q₁.cutCarrier ∧
      Disjoint P₀.closedStrip Q₁.closedStrip ∧
      IsOpen ((Subtype.val : P₀.cutCarrier → X) ⁻¹' Q₁.openStrip) ∧
      frontier Q₁.cutCarrier = (frontier P₀.cutCarrier \ Q₁.openStrip) ∪ Q₁.endDisks ∧
      Q₁.closedStrip ∩ Q₁.cutCarrier = Q₁.endDisks ∧
      Q₁.closedStrip ∪ Q₁.cutCarrier = P₀.cutCarrier ∧
      (interior Q₁.cutCarrier).Nonempty := by
  have hclosed₀ : P₀.closedStrip ⊆ P₀.map '' (Disk ×ˢ I) := by
    apply image_mono
    intro z hz
    exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hopenFull₀ : P₀.openStrip ⊆ P₀.map '' (Disk ×ˢ I) := by
    apply image_mono
    intro z hz
    exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hend₀ : P₀.endDisks ⊆ P₀.map '' (Disk ×ˢ I) := by
    rw [← P₀.closedStrip_sdiff_openStrip]
    exact sdiff_subset.trans hclosed₀
  have havoid (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) :
      P₁.map z ∉ P₀.map '' (Disk ×ˢ I) :=
    fun h => disjoint_left.mp hdis h (mem_image_of_mem P₁.map hz)
  obtain ⟨hcompact₀,hint₀,hfront₀,_,_,_⟩ := P₀.cut_geometry hR hopen₀
  have he₀ : PLDomain e P₀.cutCarrier := P₀.plDomain_cut hR he hopen₀
  let Q₁ : OriginalDiskProduct e P₀.cutCarrier j₁ := {
    map := P₁.map
    polyhedral := P₁.polyhedral
    injective := P₁.injective
    embedding := P₁.embedding
    inside := fun z hz => ⟨P₁.inside hz,fun h => havoid z hz (hopenFull₀ h)⟩
    central := P₁.central
    proper := by
      intro z hz
      rw [hfront₀]
      constructor
      · rintro (h|h)
        · exact (P₁.proper z hz).mp h.1
        · exact (havoid z hz (hend₀ h)).elim
      · intro h
        exact Or.inl ⟨(P₁.proper z hz).mpr h,fun h => havoid z hz (hopenFull₀ h)⟩ }
  have hinc : Continuous (Set.inclusion (show P₀.cutCarrier ⊆ R from sdiff_subset)) :=
    continuous_inclusion _
  have hopenQ : IsOpen ((Subtype.val : P₀.cutCarrier → X) ⁻¹' Q₁.openStrip) := by
    exact (hopen₁ (1/2) (by norm_num) (by norm_num)).preimage hinc
  obtain ⟨hcompact₁,_,hfront₁,hoverlap₁,hcover₁,hne₁⟩ := Q₁.cut_geometry hcompact₀ hopenQ
  have he₁ : PLDomain e Q₁.cutCarrier := Q₁.plDomain_cut hcompact₀ he₀ hopenQ
  refine ⟨Q₁,rfl,he₀,hcompact₀,he₁,hcompact₁,?_,hopenQ,hfront₁,hoverlap₁,hcover₁,hne₁⟩
  apply hdis.mono hclosed₀
  apply image_mono
  intro z hz
  exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩

end PoincareConjecture.M76.Dehn.Annuli
