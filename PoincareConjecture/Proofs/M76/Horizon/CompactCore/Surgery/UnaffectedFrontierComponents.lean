import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)



theorem OriginalDiskProduct.compressed_frontier_away_block
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {K F Fnew : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks) :
    Fnew \ P.closedStrip = F \ P.closedStrip := by
  have hopen : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  rw [hnew, ← P.closedStrip_sdiff_openStrip]
  ext x
  constructor
  · rintro ⟨hx | hx, hn⟩
    · exact ⟨hx.1, hn⟩
    · exact False.elim (hn hx.1)
  · rintro ⟨hx, hn⟩
    exact ⟨Or.inl ⟨hx, fun ho => hn (hopen ho)⟩, hn⟩

end PoincareConjecture.M76

namespace Set





theorem unaffected_components_of_eq_sdiff
    {X κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {F Fnew B : Set X} (hB : IsClosed B) (S : κ → Set X)
    (hcompact : ∀ i, IsCompact (S i)) (hconn : ∀ i, IsConnected (S i))
    (hcover : (⋃ i, S i) = F)
    (hcomponent : ∀ i, ∀ x ∈ S i, connectedComponentIn F x = S i)
    (haway : Fnew \ B = F \ B) :
    ∀ i, Disjoint (S i) B →
      S i ⊆ Fnew ∧
      IsClopen ((Subtype.val : Fnew → X) ⁻¹' S i) ∧
      ∀ x ∈ S i, connectedComponentIn Fnew x = S i := by
  classical
  intro i hdisj
  let others := ⋃ k : {k : κ // S k ≠ S i}, S k.val
  let rest := others ∪ B
  have hothers : IsClosed others := isClosed_iUnion_of_finite (fun k => (hcompact k.val).isClosed)
  have hrest : IsClosed rest := hothers.union hB
  have hSiF : S i ⊆ F := fun _ hx => hcover.subset (mem_iUnion.mpr ⟨i, hx⟩)
  have hotherdisj : Disjoint (S i) others := by
    apply disjoint_left.mpr
    intro x hx hxother
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxother
    exact k.property ((hcomponent k.val x hk).symm.trans (hcomponent i x hx))
  have hrestdisj : Disjoint (S i) rest := disjoint_union_right.mpr ⟨hotherdisj, hdisj⟩
  have hSiNew : S i ⊆ Fnew := by
    intro x hx
    have hxaway : x ∈ F \ B := ⟨hSiF hx, fun hb => disjoint_left.mp hdisj hx hb⟩
    exact (haway.symm ▸ hxaway).1
  have hnewcover : Fnew ⊆ S i ∪ rest := by
    intro x hx
    by_cases hb : x ∈ B
    · exact Or.inr (Or.inr hb)
    · have hxF : x ∈ F := (haway ▸ (show x ∈ Fnew \ B from ⟨hx, hb⟩)).1
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover.symm.subset hxF)
      by_cases hki : S k = S i
      · exact Or.inl (hki ▸ hk)
      · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩))
  have hclopen : IsClopen ((Subtype.val : Fnew → X) ⁻¹' S i) := by
    refine ⟨(hcompact i).isClosed.preimage continuous_subtype_val, ?_⟩
    have heq : ((Subtype.val : Fnew → X) ⁻¹' S i)ᶜ =
        (Subtype.val : Fnew → X) ⁻¹' rest := by
      ext x
      constructor
      · intro hx
        exact (hnewcover x.property).resolve_left hx
      · exact fun hx hs => disjoint_left.mp hrestdisj hs hx
    apply isClosed_compl_iff.mp
    rw [heq]
    exact hrest.preimage continuous_subtype_val
  refine ⟨hSiNew, hclopen, ?_⟩
  intro x hx
  apply Subset.antisymm
  · have hside := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isConnected_connectedComponentIn_iff.mpr (hSiNew hx)).isPreconnected
      (S i) rest (hcompact i).isClosed hrest
      ((connectedComponentIn_subset Fnew x).trans hnewcover)
      (by rw [disjoint_iff_inter_eq_empty.mp hrestdisj, inter_empty])
    rcases hside with hs | hr
    · exact hs
    · exact False.elim (disjoint_left.mp hrestdisj hx (hr (mem_connectedComponentIn (hSiNew hx))))
  · exact (hconn i).isPreconnected.subset_connectedComponentIn hx hSiNew

end Set

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)





theorem OriginalDiskProduct.unaffected_frontier_components
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {K F Fnew : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (S : κ → Set X)
    (hcompact : ∀ i, IsCompact (S i)) (hconn : ∀ i, IsConnected (S i))
    (hcover : (⋃ i, S i) = F)
    (hcomponent : ∀ i, ∀ x ∈ S i, connectedComponentIn F x = S i)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks) :
    ∀ i, Disjoint (S i) P.closedStrip →
      S i ⊆ Fnew ∧
      IsClopen ((Subtype.val : Fnew → X) ⁻¹' S i) ∧
      ∀ x ∈ S i, connectedComponentIn Fnew x = S i :=
  Set.unaffected_components_of_eq_sdiff
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    S hcompact hconn hcover hcomponent (P.compressed_frontier_away_block hnew)




theorem OriginalDiskProduct.new_frontier_components_avoiding_caps
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {K F Fnew : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (S : κ → Set X)
    (hcompact : ∀ i, IsCompact (S i)) (hconn : ∀ i, IsConnected (S i))
    (hcover : (⋃ i, S i) = Fnew)
    (hcomponent : ∀ i, ∀ x ∈ S i, connectedComponentIn Fnew x = S i)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks) :
    ∀ i, Disjoint (S i) P.endDisks →
      S i ⊆ F ∧
      IsClopen ((Subtype.val : F → X) ⁻¹' S i) ∧
      ∀ x ∈ S i, connectedComponentIn F x = S i := by
  intro i hcaps
  have hSiNew : S i ⊆ Fnew := fun _ hx => hcover.subset (mem_iUnion.mpr ⟨i, hx⟩)
  have hblock : Disjoint (S i) P.closedStrip := by
    apply disjoint_left.mpr
    intro x hx hb
    exact disjoint_left.mp hcaps hx ((P.compressed_frontier_inter_block hnew).subset ⟨hSiNew hx, hb⟩)
  exact Set.unaffected_components_of_eq_sdiff
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
    S hcompact hconn hcover hcomponent (P.compressed_frontier_away_block hnew).symm i hblock

end PoincareConjecture.M76
