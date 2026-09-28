import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FiniteCapComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedAttachmentComponentCarriers








set_option autoImplicit false
open Set Geometry Topology

namespace Set

local notation "V3" => (Fin 3 → ℝ)



theorem componentIn_finite_cap_attachment
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ]
    {P : Set E} (D B : κ → Set E)
    (hP : IsClosed P) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hattach : ∀ i, P ∩ D i = B i) {x : E} (hx : x ∈ P) :
    connectedComponentIn (P ∪ ⋃ i, D i) x = connectedComponentIn P x ∪
      ⋃ i ∈ {i | (B i ∩ connectedComponentIn P x).Nonempty}, D i := by
  obtain ⟨H, hH⟩ := exists_components_homeomorph_finite_cap_attachment
    D B hP hD hdis hattach
  have hold {y : E} (hy : y ∈ P) :
      y ∈ connectedComponentIn (P ∪ ⋃ i, D i) x ↔
        y ∈ connectedComponentIn P x := by
    rw [mem_componentIn_iff_component_class (P := P ∪ ⋃ i, D i)
        (x := x) (y := y) (Or.inl hx) (Or.inl hy),
      mem_componentIn_iff_component_class (P := P) (x := x) (y := y) hx hy,
      ← hH ⟨y, hy⟩, ← hH ⟨x, hx⟩]
    exact H.injective.eq_iff
  have hcap {i : κ} {y : E} (hy : y ∈ D i) :
      D i ⊆ connectedComponentIn (P ∪ ⋃ j, D j) y :=
    (hD i).isConnected.isPreconnected.subset_connectedComponentIn hy
      (fun _ hz => Or.inr (mem_iUnion.mpr ⟨i, hz⟩))
  apply Subset.antisymm
  · intro y hy
    rcases connectedComponentIn_subset _ _ hy with hyP | hyD
    · exact Or.inl ((hold hyP).mp hy)
    · obtain ⟨i, hyi⟩ := mem_iUnion.mp hyD
      obtain ⟨b, hb⟩ := (hD i).isConnected_boundary_three.nonempty
      have hbPD := (hattach i).symm.subset hb
      have hbnew : b ∈ connectedComponentIn (P ∪ ⋃ j, D j) x := by
        rw [connectedComponentIn_eq hy]
        exact hcap hyi hbPD.2
      exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨b, hb, (hold hbPD.1).mp hbnew⟩, hyi⟩)
  · apply union_subset
    · exact connectedComponentIn_mono x subset_union_left
    · intro y hy
      obtain ⟨i, ⟨b, hb, hbx⟩, hyi⟩ := mem_iUnion₂.mp hy
      have hbnew := connectedComponentIn_mono x
        (show P ⊆ P ∪ ⋃ j, D j from subset_union_left) hbx
      rw [connectedComponentIn_eq hbnew]
      exact hcap ((hattach i).symm.subset hb).2 hyi

end Set
