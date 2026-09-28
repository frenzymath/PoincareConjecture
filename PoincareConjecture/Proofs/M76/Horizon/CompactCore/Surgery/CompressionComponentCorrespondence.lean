import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionOldComponent
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapComponents
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.UnaffectedFrontierComponents









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1




theorem exists_unaffected_component_correspondence
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    {n m : ℕ} (S : Fin n → Set X) (T : Fin m → Set X)
    (hScompact : ∀ i, IsCompact (S i)) (hSconn : ∀ i, IsConnected (S i))
    (hScover : (⋃ i, S i) = F)
    (hScomponents : ∀ i, ∀ x ∈ S i, connectedComponentIn F x = S i)
    (hSdisjoint : Pairwise fun i k => Disjoint (S i) (S k))
    (hTcompact : ∀ k, IsCompact (T k)) (hTconn : ∀ k, IsConnected (T k))
    (hTcover : (⋃ k, T k) = Fnew)
    (hTcomponents : ∀ k, ∀ x ∈ T k, connectedComponentIn Fnew x = T k)
    (hTdisjoint : Pairwise fun k l => Disjoint (T k) (T l)) :
    ∃ (c : Fin n) (q : Bool → Fin m)
      (E : {i : Fin n // i ≠ c} ≃ {k : Fin m // k ≠ q false ∧ k ≠ q true}),
      (F ∩ P.closedStrip).Nonempty ∧
      F ∩ P.closedStrip ⊆ S c ∧
      (∀ i, F ∩ P.closedStrip ⊆ S i ↔ c = i) ∧
      (∀ b, P.capDisk b ⊆ T (q b)) ∧
      (∀ b k, P.capDisk b ⊆ T k ↔ q b = k) ∧
      (∀ i, i ≠ c → Disjoint (S i) P.closedStrip) ∧
      (∀ k, k ≠ q false → k ≠ q true → Disjoint (T k) P.closedStrip) ∧
      ∀ i, S i.val = T (E i).val := by
  classical
  obtain ⟨c, _, _, hannulus, hSc, hcunique, hSmiss, _, _⟩ :=
    P.exists_old_component_label hcut hsmall S hScover hScomponents hSdisjoint
  obtain ⟨q, hcap, hqunique, _⟩ :=
    P.exists_cap_component_labels hnew T hTcover hTcomponents hTdisjoint
  have hcapblock (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    intro y hy
    apply P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b with
    | false => exact Or.inl hy
    | true => exact Or.inr hy
  have hTmiss (k : Fin m) (hk0 : k ≠ q false) (hk1 : k ≠ q true) :
      Disjoint (T k) P.endDisks ∧ Disjoint (T k) P.closedStrip := by
    have hcaps : Disjoint (T k) P.endDisks := by
      rw [P.endDisks_eq_capDisks]
      exact disjoint_union_right.mpr
        ⟨(hTdisjoint hk0).mono_right (hcap false), (hTdisjoint hk1).mono_right (hcap true)⟩
    refine ⟨hcaps, disjoint_left.mpr ?_⟩
    intro x hx hblock
    have hxNew : x ∈ Fnew := hTcover.subset (mem_iUnion.mpr ⟨k, hx⟩)
    exact disjoint_left.mp hcaps hx
      ((P.compressed_frontier_inter_block hnew).subset ⟨hxNew, hblock⟩)
  have hforward (i : {i : Fin n // i ≠ c}) :
      ∃ k : {k : Fin m // k ≠ q false ∧ k ≠ q true}, S i.val = T k.val := by
    obtain ⟨hSiNew, _, hSiWhole⟩ := P.unaffected_frontier_components S hScompact hSconn
      hScover hScomponents hnew i.val (hSmiss i.val i.property)
    obtain ⟨x, hx⟩ := (hSconn i.val).nonempty
    obtain ⟨k, hxk⟩ := mem_iUnion.mp (hTcover.symm.subset (hSiNew hx))
    have heq : S i.val = T k := (hSiWhole x hx).symm.trans (hTcomponents k x hxk)
    have hk (b : Bool) : k ≠ q b := by
      intro hkq
      obtain ⟨y, hy⟩ := (P.isConnected_capDisk b).nonempty
      have hyTk : y ∈ T k := hkq.symm ▸ hcap b hy
      exact disjoint_left.mp (hSmiss i.val i.property) (heq.symm ▸ hyTk) (hcapblock b hy)
    exact ⟨⟨k, hk false, hk true⟩, heq⟩
  have hbackward (k : {k : Fin m // k ≠ q false ∧ k ≠ q true}) :
      ∃ i : {i : Fin n // i ≠ c}, S i.val = T k.val := by
    obtain ⟨hTkF, _, hTkWhole⟩ := P.new_frontier_components_avoiding_caps T hTcompact hTconn
      hTcover hTcomponents hnew k.val (hTmiss k.val k.property.1 k.property.2).1
    obtain ⟨x, hx⟩ := (hTconn k.val).nonempty
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hScover.symm.subset (hTkF hx))
    have heq : S i = T k.val := (hScomponents i x hxi).symm.trans (hTkWhole x hx)
    have hi : i ≠ c := by
      intro hic
      obtain ⟨y, hy⟩ := hannulus
      have hySi : y ∈ S i := hic.symm ▸ hSc hy
      exact disjoint_left.mp (hTmiss k.val k.property.1 k.property.2).2
        (heq ▸ hySi) hy.2
    exact ⟨⟨i, hi⟩, heq⟩
  choose f hf using hforward
  have hfinj : Function.Injective f := by
    intro i l hil
    apply Subtype.ext
    by_contra hne
    obtain ⟨x, hx⟩ := (hSconn i.val).nonempty
    have heq : S i.val = S l.val := (hf i).trans ((congrArg (fun k => T k.val) hil).trans (hf l).symm)
    exact disjoint_left.mp (hSdisjoint hne) hx (heq ▸ hx)
  have hfsurj : Function.Surjective f := by
    intro k
    obtain ⟨i, hi⟩ := hbackward k
    refine ⟨i, Subtype.ext ?_⟩
    by_contra hne
    obtain ⟨x, hx⟩ := (hSconn i.val).nonempty
    exact disjoint_left.mp (hTdisjoint hne) ((hf i) ▸ hx) (hi ▸ hx)
  let E := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  exact ⟨c, q, E, hannulus, hSc, hcunique, hcap, hqunique, hSmiss,
    fun k hk0 hk1 => (hTmiss k hk0 hk1).2, hf⟩

end PoincareConjecture.M76.OriginalDiskProduct
