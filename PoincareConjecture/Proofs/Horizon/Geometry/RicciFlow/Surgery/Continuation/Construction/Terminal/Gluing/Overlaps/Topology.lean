import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Overlaps.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Gluing.Separation








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} {X : Type v} {Y : ι → Type v}
  [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
  [T2Space X] [∀ i, T2Space (Y i)]
  (e : ∀ i, OpenPartialHomeomorph X (Y i))
  (hd : Pairwise (fun i j => Disjoint (e i).source (e j).source))
  (hc : ∀ i, IsClosed {p : X × Y i | p.1 ∈ (e i).source ∧ e i p.1 = p.2})

omit [T2Space X] [∀ i, T2Space (Y i)] in
include hc in
theorem isClosed_inverse_graph (i : ι) :
    IsClosed {p : Y i × X | p.1 ∈ (e i).target ∧ (e i).symm p.1 = p.2} := by
  have heq : {p : Y i × X | p.1 ∈ (e i).target ∧ (e i).symm p.1 = p.2} =
      Prod.swap ⁻¹' {p : X × Y i | p.1 ∈ (e i).source ∧ e i p.1 = p.2} := by
    ext p
    change (p.1 ∈ (e i).target ∧ (e i).symm p.1 = p.2) ↔
      (p.2 ∈ (e i).source ∧ e i p.2 = p.1)
    constructor
    · rintro ⟨hp, he⟩
      exact ⟨he ▸ (e i).map_target hp, he ▸ (e i).right_inv hp⟩
    · rintro ⟨hp, he⟩
      exact ⟨he ▸ (e i).map_source hp, by rw [← he, (e i).left_inv hp]⟩
  rw [heq]
  exact (hc i).preimage continuous_swap

include hc in
theorem overlaps_closed (i j : Option ι) :
    IsClosed {p : Piece X Y i × Piece X Y j |
      (overlaps e hd).Rel ⟨i, p.1⟩ ⟨j, p.2⟩} := by
  cases i with
  | none =>
    cases j with
    | none =>
      simpa [Poincare.Gluing.OverlapSystem.Rel, overlaps, transition] using
        (isClosed_eq (continuous_fst : Continuous (Prod.fst : X × X → X)) continuous_snd)
    | some j => exact hc j
  | some i =>
    cases j with
    | none => exact isClosed_inverse_graph e hc i
    | some j =>
      by_cases h : i = j
      · subst j
        simpa [Poincare.Gluing.OverlapSystem.Rel, overlaps, transition] using
          (isClosed_eq (continuous_fst : Continuous (Prod.fst : Y i × Y i → Y i))
            continuous_snd)
      · have hempty : {p : Y i × Y j |
            (overlaps e hd).Rel ⟨some i, p.1⟩ ⟨some j, p.2⟩} = ∅ := by
          ext p
          change (p.1 ∈ (capTransition e i j).source ∧ _) ↔ False
          rw [capTransition_source_empty e hd h]
          simp
        rw [hempty]
        exact isClosed_empty

include hc in
theorem overlaps_t2Space : T2Space (Quotient (overlaps e hd).setoid) :=
  (overlaps e hd).quotient_t2Space (overlaps_closed e hd hc)

end PoincareConjecture.Surgery.Terminal.Gluing
