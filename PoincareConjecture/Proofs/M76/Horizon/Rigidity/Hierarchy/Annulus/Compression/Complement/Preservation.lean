import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.LocalDomains
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.PhaseArc
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X : Type*} [TopologicalSpace X] {p : ℝ} [Fact (0 < p)]

theorem circle_slab_interior_phase_iff
    (q : C(X, AddCircle p)) {R : Set X} {c a b : ℝ}
    (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ q ⁻¹' {(a : AddCircle p)}) ∪ (R ∩ q ⁻¹' {(b : AddCircle p)})))
    {x : X} (hx : x ∈ interior R) :
    x ∈ interior (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) ↔
      q x ∈ interior (AddCircle.closedIntervalArc p a b) := by
  have hxR : x ∈ R := interior_subset hx
  have hxB : x ∉ frontier R := fun h => disjoint_left.mp disjoint_interior_frontier hx h
  have hmem : x ∈ R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b ↔
      q x ∈ AddCircle.closedIntervalArc p a b := and_iff_right hxR
  have hf : x ∈ frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) ↔
      q x ∈ frontier (AddCircle.closedIntervalArc p a b) := by
    rw [hfront, AddCircle.frontier_closedIntervalArc_shifted p ha hab.le hb]
    simp only [mem_union, mem_inter_iff, hxB, and_false, false_or, mem_preimage,
      hxR, true_and, mem_singleton_iff, mem_insert_iff]
  rw [← self_sdiff_frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b),
    ← self_sdiff_frontier (AddCircle.closedIntervalArc p a b)]
  exact and_congr hmem (not_congr hf)

theorem complementary_circle_slab_agrees_exterior
    (q : C(X, AddCircle p)) {R : Set X} {c a b : ℝ}
    (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ q ⁻¹' {(a : AddCircle p)}) ∪ (R ∩ q ⁻¹' {(b : AddCircle p)}))) :
    ∀ x ∈ interior R,
      x ∈ R ∩ q ⁻¹' AddCircle.closedIntervalArc p b (a + p) ↔
        x ∈ (interior (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b))ᶜ := by
  intro x hx
  rw [← HamiltonIntervalTorus.compl_interior_shifted_phase_arc p ha hab hb]
  change (x ∈ R ∧ q x ∉ interior (AddCircle.closedIntervalArc p a b)) ↔ _
  rw [and_iff_right (interior_subset hx)]
  exact (not_congr (circle_slab_interior_phase_iff q ha hab hb hfront hx)).symm

theorem frontier_complementary_circle_slab
    {ι : Type*} {e : ι → OpenPartialHomeomorph X V3}
    (q : C(X, AddCircle p)) {R : Set X} (hR : IsClosed R) {c a b : ℝ}
    (ha : c < a) (hab : a < b) (hb : b < c + p)
    (he : PLDomain e (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ q ⁻¹' {(a : AddCircle p)}) ∪ (R ∩ q ⁻¹' {(b : AddCircle p)}))) :
    frontier (R ∩ q ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
      ((R ∩ q ⁻¹' AddCircle.closedIntervalArc p b (a + p)) ∩ frontier R) ∪
        ((R ∩ q ⁻¹' {(a : AddCircle p)}) ∪ (R ∩ q ⁻¹' {(b : AddCircle p)})) := by
  let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
  let C := R ∩ q ⁻¹' AddCircle.closedIntervalArc p b (a + p)
  have hclosed : IsClosed C := hR.inter
    ((AddCircle.isCompact_closedIntervalArc p b (a + p)).isClosed.preimage q.continuous)
  have hlocal (x : X) (hx : x ∈ interior R) : x ∈ frontier C ↔ x ∈ frontier N := by
    have h := HamiltonIntervalTorus.mem_frontier_iff_of_open_agreement isOpen_interior
      (complementary_circle_slab_agrees_exterior q ha hab hb hfront) hx
    rwa [he.frontier_closed_exterior] at h
  have hold (x : X) (hx : x ∈ C) (hxI : x ∉ interior R) : x ∈ frontier C := by
    apply (mem_frontier_iff_notMem_interior hx).mpr
    exact fun h => hxI (interior_mono inter_subset_left h)
  have hends : (R ∩ q ⁻¹' {(a : AddCircle p)}) ∪
      (R ∩ q ⁻¹' {(b : AddCircle p)}) ⊆ C := by
    intro x hx
    rcases hx with hx | hx
    · refine ⟨hx.1, ?_⟩
      change q x ∈ AddCircle.closedIntervalArc p b (a + p)
      rw [show q x = (a : AddCircle p) from hx.2]
      exact ⟨a + p, ⟨by linarith, le_rfl⟩, AddCircle.coe_add_period p a⟩
    · refine ⟨hx.1, ?_⟩
      change q x ∈ AddCircle.closedIntervalArc p b (a + p)
      rw [show q x = (b : AddCircle p) from hx.2]
      exact ⟨b, ⟨le_rfl, by linarith⟩, rfl⟩
  apply Subset.antisymm
  · intro x hx
    by_cases hxI : x ∈ interior R
    · have hf := (hlocal x hxI).mp hx
      rw [hfront] at hf
      rcases hf with hf | hf
      · exact (disjoint_left.mp disjoint_interior_frontier hxI hf.2).elim
      · exact Or.inr hf
    · have hxC := hclosed.frontier_subset hx
      exact Or.inl ⟨hxC, (mem_frontier_iff_notMem_interior hxC.1).mpr hxI⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hold x hx.1 (fun h => disjoint_left.mp disjoint_interior_frontier h hx.2)
    · by_cases hxI : x ∈ interior R
      · exact (hlocal x hxI).mpr (hfront.symm.subset (Or.inr hx))
      · exact hold x (hends hx) hxI

theorem plDomain_complementary_circle_slab_of_supported_map
    {ι : Type*} {e : ι → OpenPartialHomeomorph X V3}
    (q0 q1 : C(X, AddCircle p)) {R : Set X} (hR : IsClosed R) {c a b : ℝ}
    (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hold : PLDomain e (R ∩ q0 ⁻¹' AddCircle.closedIntervalArc p b (a + p)))
    (hnew : PLDomain e (R ∩ q1 ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ q1 ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ q1 ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ q1 ⁻¹' {(a : AddCircle p)}) ∪ (R ∩ q1 ⁻¹' {(b : AddCircle p)})))
    {A : Set X} (hA : IsClosed A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, q1 x = q0 x) :
    PLDomain e (R ∩ q1 ⁻¹' AddCircle.closedIntervalArc p b (a + p)) := by
  have hclosed : IsClosed (R ∩ q1 ⁻¹' AddCircle.closedIntervalArc p b (a + p)) :=
    hR.inter ((AddCircle.isCompact_closedIntervalArc p b (a + p)).isClosed.preimage q1.continuous)
  apply HamiltonIntervalTorus.plDomain_of_two_open_agreements hnew.closed_exterior hold hclosed
    isOpen_interior hA.isOpen_compl
  · intro x _
    by_cases hx : x ∈ interior R
    · exact Or.inl hx
    · exact Or.inr (fun h => hx (hAR h))
  · exact complementary_circle_slab_agrees_exterior q1 ha hab hb hfront
  · intro x hx
    change (x ∈ R ∧ q1 x ∈ AddCircle.closedIntervalArc p b (a + p)) ↔
      (x ∈ R ∧ q0 x ∈ AddCircle.closedIntervalArc p b (a + p))
    rw [hfixed x hx]

end PoincareConjecture.M76
