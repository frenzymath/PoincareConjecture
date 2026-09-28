import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CyclicOneBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CyclicTwoBoundary
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
open Set Metric Geometry AbstractSimplicialComplex PLAnnularStrip
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical in
theorem boundary_circle_count_eq_two_of_nontrivial_isCyclic_and_geometric_signs
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype β] [Nonempty β]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (L : β → SimplicialComplex ℝ E) (hLK : ∀ i, L i ≤ K)
    (hdis : Pairwise (fun i j => Disjoint (L i).space (L j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (L i).faces then 1 else 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)]
    [Nontrivial (FundamentalGroup K.space x)] : Nat.card β = 2 := by
  have hle := boundary_circle_count_le_two_of_isCyclic K hK hpure hconn hlinks
    L hLK hdis gamma hgamma hcofaces x
  have hpos := Nat.card_pos (α := β)
  suffices hne : Nat.card β ≠ 1 by omega
  intro hone
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp
    (show Fintype.card β = 1 by simpa only [Nat.card_eq_fintype_card] using hone)
  have hboundary (s : Finset E) (hs : s ∈ K.faces) (hsc : s.card = 2) :
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ (L i).faces then 1 else 2 := by
    have he : (∃ j, s ∈ (L j).faces) ↔ s ∈ (L i).faces := by
      constructor
      · rintro ⟨j, hj⟩
        simpa only [hi j] using hj
      · exact fun h => ⟨i, h⟩
    simpa only [he] using hcofaces s hs hsc
  obtain ⟨_, C, _, hC, hCne, H, _, _⟩ :=
    isFinitePLBallPair_of_isCyclic_and_one_oriented_boundary K (L i) hK hpure
      hlinks hconn (hLK i) (gamma i) (hgamma i) hboundary number hnumber sign hcancel x
  let : ContractibleSpace C := hC.contractibleSpace (hCne.mono interior_subset)
  let : ContractibleSpace K.space := H.contractibleSpace
  obtain ⟨a, b, hab⟩ := exists_pair_ne (FundamentalGroup K.space x)
  exact hab (Subsingleton.elim a b)

open Classical in
theorem exists_marked_annulus_of_nontrivial_isCyclic_and_geometric_signs
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype β] [Nonempty β]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (L : β → SimplicialComplex ℝ E) (hLK : ∀ i, L i ≤ K)
    (hdis : Pairwise (fun i j => Disjoint (L i).space (L j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (L i).faces then 1 else 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)]
    [Nontrivial (FundamentalGroup K.space x)] :
    ∃ order : Bool ≃ β, ∃ A : squareAnnulus 8 1 ≃ₜ K.space, A.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔
        (A p : E) ∈ (L (order false)).space) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔
        (A p : E) ∈ (L (order true)).space) := by
  have hcount := boundary_circle_count_eq_two_of_nontrivial_isCyclic_and_geometric_signs
    K hK hpure hconn hlinks L hLK hdis gamma hgamma hcofaces
    number hnumber sign hcancel x
  let order : Bool ≃ β := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_bool, Nat.card_eq_fintype_card] using hcount.symm)
  refine ⟨order, ?_⟩
  apply exists_annulus_of_isCyclic_and_two_boundaries K hK hpure hlinks hconn
    (L ∘ order) (fun b => hLK (order b)) (fun b => gamma (order b))
    (fun b => hgamma (order b))
    (hdis (fun h => Bool.false_ne_true (order.injective h))) ?_ x
  intro s hs hsc
  have he : (∃ b : Bool, s ∈ (L (order b)).faces) ↔ ∃ i, s ∈ (L i).faces := by
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨order b, hb⟩
    · rintro ⟨i, hi⟩
      exact ⟨order.symm i, by simpa using hi⟩
  simpa only [Function.comp_apply, he] using hcofaces s hs hsc

end PoincareConjecture.M76
