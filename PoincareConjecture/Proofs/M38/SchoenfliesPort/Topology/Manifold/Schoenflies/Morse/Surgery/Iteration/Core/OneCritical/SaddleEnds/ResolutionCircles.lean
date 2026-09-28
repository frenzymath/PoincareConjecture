import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ComponentCount







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies








noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem index_two_component_family
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (R : I → Set X) {L : Set X} (hR : (⋃ i, R i) = L)
    (hcomponent : ∀ i p, p ∈ R i → R i = connectedComponentIn L p)
    (hcard : Nat.card I = 2)
    (C : Fin 2 → Set X) (hC : ∀ i p, p ∈ C i → connectedComponentIn L p = C i)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (p : Fin 2 → X) (hp : ∀ i, p i ∈ C i) (hpL : ∀ i, p i ∈ L) :
    ∃ E : Fin 2 ≃ I, ∀ i, R (E i) = C i := by
  classical
  let := Fintype.ofFinite I
  choose k hk using fun i => mem_iUnion.mp (hR.superset (hpL i))
  have heq (i : Fin 2) : R (k i) = C i :=
    (hcomponent (k i) (p i) (hk i)).trans (hC i (p i) (hp i))
  have hinj : Injective k := by
    intro i j hij
    by_contra hne
    have hm : p i ∈ C j := (heq j).subset (hij ▸ (heq i).superset (hp i))
    exact disjoint_left.mp (hdisjoint hne) (hp i) hm
  have hcards : Fintype.card (Fin 2) = Fintype.card I := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hcard.symm
  exact ⟨Equiv.ofBijective k ((Fintype.bijective_iff_injective_and_card k).mpr
    ⟨hinj, hcards⟩), heq⟩

variable {v : E3} {g : S2 → E3} {B : Set Real} {K : Set S2}



theorem exists_lowerCutCircle_equiv_of_two_components
    (A : AnnularEndFamily v g B K)
    (hcard : Nat.card (ConnectedComponents {q | inner Real v (g q) = A.lowerCut}) = 2)
    (C : Fin 2 → Set S2)
    (hC : ∀ i q, q ∈ C i →
      connectedComponentIn {q | inner Real v (g q) = A.lowerCut} q = C i)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (p : Fin 2 → S2) (hp : ∀ i, p i ∈ C i) :
    ∃ E : Fin 2 ≃ A.LowerCutIndex, ∀ i, range (A.lowerCutCircle (E i)) = C i := by
  have hpL (i : Fin 2) : inner Real v (g (p i)) = A.lowerCut := by
    have hm : p i ∈ connectedComponentIn {q | inner Real v (g q) = A.lowerCut} (p i) :=
      (hC i (p i) (hp i)).symm ▸ hp i
    exact connectedComponentIn_subset {q | inner Real v (g q) = A.lowerCut} (p i) hm
  exact index_two_component_family (fun i => range (A.lowerCutCircle i))
    A.iUnion_range_lowerCutCircle
    (fun i q hq => A.lowerCutCircle_range_eq_connectedComponentIn i hq)
    (A.card_lowerCutIndex_eq_two_of_card_connectedComponents hcard)
    C hC hdisjoint p hp hpL

theorem exists_upperCutCircle_equiv_of_two_components
    (A : AnnularEndFamily v g B K)
    (hcard : Nat.card (ConnectedComponents {q | inner Real v (g q) = A.upperCut}) = 2)
    (C : Fin 2 → Set S2)
    (hC : ∀ i q, q ∈ C i →
      connectedComponentIn {q | inner Real v (g q) = A.upperCut} q = C i)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (p : Fin 2 → S2) (hp : ∀ i, p i ∈ C i) :
    ∃ E : Fin 2 ≃ A.UpperCutIndex, ∀ i, range (A.upperCutCircle (E i)) = C i := by
  have hpL (i : Fin 2) : inner Real v (g (p i)) = A.upperCut := by
    have hm : p i ∈ connectedComponentIn {q | inner Real v (g q) = A.upperCut} (p i) :=
      (hC i (p i) (hp i)).symm ▸ hp i
    exact connectedComponentIn_subset {q | inner Real v (g q) = A.upperCut} (p i) hm
  exact index_two_component_family (fun i => range (A.upperCutCircle i))
    A.iUnion_range_upperCutCircle
    (fun i q hq => A.upperCutCircle_range_eq_connectedComponentIn i hq)
    (A.card_upperCutIndex_eq_two_of_card_connectedComponents hcard)
    C hC hdisjoint p hp hpL

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

end

end M38Schoenflies
