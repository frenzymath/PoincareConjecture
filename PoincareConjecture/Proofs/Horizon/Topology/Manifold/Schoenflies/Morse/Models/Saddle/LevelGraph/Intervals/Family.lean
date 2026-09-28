import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Contacts
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FiniteBoundaryComponents









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1


theorem card_exterior_connectedComponents_eq_two
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    Nat.card (ConnectedComponents
      (connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r : Set S2)) = 2 := by
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  obtain ⟨hinj, hboundary, _, _, _, _⟩ :=
    compact_regular_exterior hh hunique e he0 hep hform hr hrs
  have hmem (i : Fin 2 × Fin 2) : e (contact r i) ∈ K := by
    have hi : e (contact r i) ∈ K ∩ e '' closedSquare r := by
      rw [hboundary]
      exact mem_range_self i
    exact hi.1
  let b : Fin 2 × Fin 2 → K := fun i => ⟨e (contact r i), hmem i⟩
  apply Poincare.Topology.card_connectedComponents_eq_two_of_boundary_fibers b
    (by simp [Nat.card_eq_fintype_card])
  intro q
  obtain ⟨γ, a, b, _, hγe, _, hab, _, hcontacts⟩ :=
    exists_exterior_intervals_with_contacts hh hunique e he0 hep he hei hform hr hrs
      q q.property
  exact Poincare.Topology.card_preimage_eq_two_of_range_inter_eq_pair hinj
    (fun heq => hab.ne (hγe.injective heq)) hcontacts

private theorem component_eq_of_class_eq {K : Set S2} {x y : K}
    (hxy : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    connectedComponentIn K x = connectedComponentIn K y := by
  rw [connectedComponentIn_eq_image x.property, connectedComponentIn_eq_image y.property,
    ConnectedComponents.coe_eq_coe.mp hxy]

private theorem class_eq_of_component_eq {K : Set S2} {x y : K}
    (hxy : connectedComponentIn K x = connectedComponentIn K y) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  apply ConnectedComponents.coe_eq_coe'.mpr
  have hx : (x : S2) ∈ connectedComponentIn K y := hxy ▸ mem_connectedComponentIn x.property
  rw [connectedComponentIn_eq_image y.property] at hx
  obtain ⟨z, hz, heq⟩ := hx
  have hzx : z = x := Subtype.ext heq
  exact hzx ▸ hz



theorem exists_two_exterior_intervals
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    ∃ (γ : Fin 2 → Real → S2) (a b : Fin 2 → Real),
      (∀ i, ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        (∀ t, Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 2) (γ i) t)) ∧ a i < b i) ∧
      (⋃ i, γ i '' Icc (a i) (b i)) = K ∧
      Pairwise (fun i j => Disjoint (γ i '' Icc (a i) (b i)) (γ j '' Icc (a j) (b j))) ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
        (γ i '' Icc (a i) (b i)) = {γ i (a i), γ i (b i)}) ∧
      ∀ i, ∃ q ∈ K, γ i '' Icc (a i) (b i) = connectedComponentIn K q := by
  classical
  dsimp only
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  have hcard : Nat.card (ConnectedComponents K) = 2 :=
    card_exterior_connectedComponents_eq_two hh hunique e he0 hep he hei hform hr hrs
  have hn : Nat.card (ConnectedComponents K) ≠ 0 := by rw [hcard]; decide
  let E : ConnectedComponents K ≃ Fin 2 :=
    (Nat.equivFinOfCardPos hn).trans (finCongr hcard)
  choose q hq using fun i : Fin 2 => ConnectedComponents.surjective_coe (E.symm i)
  choose γ a b hγ using fun i : Fin 2 =>
    exists_exterior_intervals_with_contacts hh hunique e he0 hep he hei hform hr hrs
      (q i) (q i).property
  have hγrange (i : Fin 2) : γ i '' Icc (a i) (b i) = connectedComponentIn K (q i) :=
    (hγ i).2.2.2.2.1
  refine ⟨γ, a, b, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hγ i).1, (hγ i).2.1, (hγ i).2.2.1, (hγ i).2.2.2.1⟩
  · apply subset_antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [hγrange i] at hi
      exact connectedComponentIn_subset K (q i) hi
    · intro x hx
      let y : K := ⟨x, hx⟩
      let i : Fin 2 := E (ConnectedComponents.mk y)
      have heq : ConnectedComponents.mk (q i) = ConnectedComponents.mk y := by
        rw [hq i]
        exact E.symm_apply_apply _
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [hγrange i, component_eq_of_class_eq heq]
      exact mem_connectedComponentIn hx
  · intro i j hij
    rw [hγrange i, hγrange j]
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have heq := (connectedComponentIn_eq hxi).trans (connectedComponentIn_eq hxj).symm
    have hc := class_eq_of_component_eq heq
    rw [hq i, hq j] at hc
    exact hij (E.symm.injective hc)
  · intro i
    rw [hγrange i]
    exact (hγ i).2.2.2.2.2
  · intro i
    exact ⟨q i, (q i).property, hγrange i⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
