import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Products.DiskBlockCoverCoordinates











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem isOpen_in_closed_union
    {X : Type*} [TopologicalSpace X] {A B V : Set X}
    (hA : IsClosed A) (hB : IsClosed B)
    (hAV : IsOpen ((Subtype.val : A → X) ⁻¹' V))
    (hBV : IsOpen ((Subtype.val : B → X) ⁻¹' V)) :
    IsOpen ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' V) := by
  have hAc : IsClosed (A \ V) := by
    have h := hA.isClosedEmbedding_subtypeVal.isClosedMap _ hAV.isClosed_compl
    have heq : (Subtype.val : A → X) '' ((Subtype.val : A → X) ⁻¹' V)ᶜ = A \ V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hx, hv⟩
        exact ⟨⟨x, hx⟩, hv, rfl⟩
    exact heq ▸ h
  have hBc : IsClosed (B \ V) := by
    have h := hB.isClosedEmbedding_subtypeVal.isClosedMap _ hBV.isClosed_compl
    have heq : (Subtype.val : B → X) '' ((Subtype.val : B → X) ⁻¹' V)ᶜ = B \ V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hx, hv⟩
        exact ⟨⟨x, hx⟩, hv, rfl⟩
    exact heq ▸ h
  apply isClosed_compl_iff.mp
  have heq : ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' V)ᶜ =
      (Subtype.val : ↥(A ∪ B) → X) ⁻¹' ((A \ V) ∪ (B \ V)) := by
    ext x
    constructor
    · intro hx
      exact x.property.elim (fun ha => Or.inl ⟨ha, hx⟩) (fun hb => Or.inr ⟨hb, hx⟩)
    · exact fun hx => hx.elim And.right And.right
  rw [heq]
  exact (hAc.union hBc).preimage continuous_subtype_val

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.frontier_block_open_cover
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (hF : IsCompact F)
    (hPF : ∀ z ∈ D ×ˢ I, P.map z ∈ F ↔ z.1 ∈ Q)
    (hlateral : IsOpen ((Subtype.val : F → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4))))) :
    let Z := F ∪ P.closedStrip
    let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
    let band := P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4))
    let U := (Subtype.val : Z → X) ⁻¹' coreᶜ
    let V := (Subtype.val : Z → X) ⁻¹' (P.closedStrip ∪ band)
    IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Disjoint F core ∧ band ⊆ F := by
  dsimp only
  let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
  let band := P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4))
  have hsmall : closedBall (0 : V2) (1 / 2) ×ˢ J ⊆ D ×ˢ I := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨closedBall_subset_closedBall (by norm_num) hx, by
      constructor <;> linarith [ht.1, ht.2]⟩
  have hcore : IsCompact core :=
    ((isCompact_closedBall (0 : V2) (1 / 2)).prod isCompact_Icc).image_of_continuousOn
      (P.polyhedral.continuousOn.mono hsmall)
  have hdisj : Disjoint F core := by
    apply disjoint_left.mpr
    rintro x hxF ⟨⟨z, t⟩, hzt, rfl⟩
    have hQ := (hPF (z, t) (hsmall hzt)).mp hxF
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hQ
    have hz : ‖z‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hzt.1
    linarith
  have hband : band ⊆ F := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    exact (hPF (z, t) ⟨sphere_subset_closedBall hz, by
      constructor <;> linarith [ht.1, ht.2]⟩).mpr hz
  have hFB : F ∩ P.closedStrip ⊆ band := by
    rintro x ⟨hxF, ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩⟩
    have hQ := (hPF (z, t) ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩).mp hxF
    exact ⟨(z, t), ⟨hQ, by constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩
  have hVF : IsOpen ((Subtype.val : F → X) ⁻¹' (P.closedStrip ∪ band)) := by
    have heq : (Subtype.val : F → X) ⁻¹' (P.closedStrip ∪ band) =
        (Subtype.val : F → X) ⁻¹' band := by
      ext x
      exact ⟨fun hx => hx.elim (fun h => hFB ⟨x.property, h⟩) id, Or.inr⟩
    rw [heq]
    exact hlateral
  have hVB : IsOpen ((Subtype.val : P.closedStrip → X) ⁻¹' (P.closedStrip ∪ band)) := by
    have heq : (Subtype.val : P.closedStrip → X) ⁻¹' (P.closedStrip ∪ band) = univ := by
      ext x
      exact ⟨fun _ => mem_univ x, fun _ => Or.inl x.property⟩
    rw [heq]
    exact isOpen_univ
  refine ⟨hcore.isClosed.isOpen_compl.preimage continuous_subtype_val,
    isOpen_in_closed_union hF.isClosed (P.isCompact_closed_strip (by norm_num)).isClosed
      hVF hVB, ?_, hdisj, hband⟩
  apply eq_univ_of_forall
  intro x
  rcases x.property with hxF | hxB
  · exact Or.inl (fun hx => disjoint_left.mp hdisj hxF hx)
  · exact Or.inr (Or.inl hxB)

theorem OriginalDiskProduct.frontier_block_cover_topology
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j)
    (hPF : ∀ z ∈ D ×ˢ I, P.map z ∈ F ↔ z.1 ∈ Q) :
    let Z := F ∪ P.closedStrip
    let core := P.map '' DiskBlockCover.core
    let V := (Subtype.val : Z → X) ⁻¹' (P.map '' DiskBlockCover.cover)
    ContractibleSpace V ∧
      IsPathConnected (((Subtype.val : Z → X) ⁻¹' coreᶜ) ∩ V) := by
  dsimp only
  let Z := F ∪ P.closedStrip
  have hcover : DiskBlockCover.cover ⊆ D ×ˢ I := by
    rintro ⟨x, t⟩ (hx | hx)
    · exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
    · exact ⟨sphere_subset_closedBall hx.1, by
        constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have hcore : DiskBlockCover.core ⊆ D ×ˢ I := by
    rintro ⟨x, t⟩ hx
    exact ⟨closedBall_subset_closedBall (by norm_num) hx.1, by
      constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have hVZ : P.map '' DiskBlockCover.cover ⊆ Z := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with hb | hl
    · exact Or.inr ⟨z, by simpa only [DiskBlockCover.block, neg_div] using hb, rfl⟩
    · exact Or.inl ((hPF z (hcover (Or.inr hl))).mpr hl.1)
  have hemb : Topology.IsEmbedding (fun z : DiskBlockCover.cover => P.map z) :=
    P.embedding.isEmbedding.comp (Topology.IsEmbedding.inclusion hcover)
  have hrange : range (fun z : DiskBlockCover.cover => P.map z) =
      P.map '' DiskBlockCover.cover := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let H : DiskBlockCover.cover ≃ₜ (P.map '' DiskBlockCover.cover) :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let : ContractibleSpace DiskBlockCover.cover := DiskBlockCover.contractible_cover
  let : ContractibleSpace (P.map '' DiskBlockCover.cover) := H.symm.contractibleSpace
  let T : ((Subtype.val : Z → X) ⁻¹' (P.map '' DiskBlockCover.cover)) ≃ₜ
      (P.map '' DiskBlockCover.cover) :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by simpa using hVZ)
  refine ⟨T.contractibleSpace, ?_⟩
  have himage : P.map '' (DiskBlockCover.cover \ DiskBlockCover.core) =
      (P.map '' DiskBlockCover.cover) \ (P.map '' DiskBlockCover.core) := by
    ext x
    constructor
    · rintro ⟨z, ⟨hz, hn⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rintro ⟨w, hw, heq⟩
      exact hn ((P.injective (hcore hw) (hcover hz) heq) ▸ hw)
    · rintro ⟨⟨z, hz, rfl⟩, hn⟩
      exact ⟨z, ⟨hz, fun hc => hn ⟨z, hc, rfl⟩⟩, rfl⟩
  have hp : IsPathConnected (P.map '' (DiskBlockCover.cover \ DiskBlockCover.core)) :=
    DiskBlockCover.isPathConnected_cover_sdiff_core.image'
      (P.polyhedral.continuousOn.mono (sdiff_subset.trans hcover))
  have hpZ := hp.preimage_coe ((image_mono sdiff_subset).trans hVZ)
  have heq : ((Subtype.val : Z → X) ⁻¹' (P.map '' DiskBlockCover.core)ᶜ) ∩
      ((Subtype.val : Z → X) ⁻¹' (P.map '' DiskBlockCover.cover)) =
      (Subtype.val : Z → X) ⁻¹' (P.map '' (DiskBlockCover.cover \ DiskBlockCover.core)) := by
    rw [himage]
    ext x
    exact and_comm
  rw [heq]
  exact hpZ

end PoincareConjecture.M76
