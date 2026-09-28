import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.SeparatingCapSphereExclusion

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_cap_component_labels
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L F Fnew : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    {n : ℕ} (S : Fin n → Set X) (hcover : (⋃ i, S i) = Fnew)
    (hcomponents : ∀ i, ∀ y ∈ S i, connectedComponentIn Fnew y = S i)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ labels : Bool → Fin n,
      (∀ b, P.capDisk b ⊆ S (labels b)) ∧
      (∀ b i, P.capDisk b ⊆ S i ↔ labels b = i) ∧
      (labels false ≠ labels true →
        ∀ b, Disjoint (S (labels b)) (P.capDisk (!b))) := by
  have hcapNew (b : Bool) : P.capDisk b ⊆ Fnew := by
    intro y hy
    apply hnew.symm.subset
    apply Or.inr
    rw [P.endDisks_eq_capDisks]
    cases b with
    | false => exact Or.inl hy
    | true => exact Or.inr hy
  have hlabel (b : Bool) : ∃ i, P.capDisk b ⊆ S i := by
    obtain ⟨y, hy⟩ := (P.isConnected_capDisk b).nonempty
    obtain ⟨i, hiy⟩ := mem_iUnion.mp (hcover.symm.subset (hcapNew b hy))
    exact ⟨i, ((P.isConnected_capDisk b).isPreconnected.subset_connectedComponentIn
      hy (hcapNew b)).trans (hcomponents i y hiy).subset⟩
  choose labels hlabels using hlabel
  refine ⟨labels, hlabels, ?_, ?_⟩
  · intro b i
    constructor
    · intro hi
      by_contra hne
      obtain ⟨y, hy⟩ := (P.isConnected_capDisk b).nonempty
      exact disjoint_left.mp (hdisjoint hne) (hlabels b hy) (hi hy)
    · intro hi
      exact hi ▸ hlabels b
  · intro hne b
    have hne' : labels b ≠ labels (!b) := by
      cases b with
      | false => exact hne
      | true => exact Ne.symm hne
    exact (hdisjoint hne').mono_right (hlabels (!b))

theorem exists_cap_component_labels_not_spherical_of_separating
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    {n : ℕ} (S : Fin n → Set X) (hcover : (⋃ i, S i) = Fnew)
    (hcomponents : ∀ i, ∀ y ∈ S i, connectedComponentIn Fnew y = S i)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (hN : PLDomain e N) (hNc : IsCompact N) (hFN : Fnew ⊆ N) :
    ∃ labels : Bool → Fin n,
      (∀ b, P.capDisk b ⊆ S (labels b)) ∧
      (∀ b i, P.capDisk b ⊆ S i ↔ labels b = i) ∧
      (labels false ≠ labels true →
        ∀ b, Disjoint (S (labels b)) (P.capDisk (!b))) ∧
      (labels false ≠ labels true →
        ∀ b, ¬ Nonempty (ChartwisePLSphere e (S (labels b)))) := by
  obtain ⟨labels, hcap, hlabels, hopposite⟩ :=
    P.exists_cap_component_labels hnew S hcover hcomponents hdisjoint
  refine ⟨labels, hcap, hlabels, hopposite, ?_⟩
  intro hne b
  have hSF : S (labels b) ⊆ Fnew := by
    intro y hy
    exact hcover.subset (mem_iUnion.mpr ⟨labels b, hy⟩)
  exact P.cap_component_not_sphere hcut hsmall hnew hSF (hcomponents (labels b))
    b (hcap b) (hopposite hne b) rim hrim hessential hN hNc (hSF.trans hFN)

end PoincareConjecture.M76.OriginalDiskProduct
