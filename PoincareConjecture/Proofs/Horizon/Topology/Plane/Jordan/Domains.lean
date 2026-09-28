import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Basic

namespace Poincare.Topology.Plane.Jordan

open Metric Set Function Bornology

theorem isConnected_compl_image_Icc
    {f : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Icc (0 : ℝ) 1)) :
    IsConnected (f '' Icc (0 : ℝ) 1)ᶜ := by
  let e : unitInterval ≃ₜ (f '' Icc (0 : ℝ) 1) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn f (Icc (0 : ℝ) 1) hinj)
      (continuous_induced_rng.2 hf.domRestrict)
  exact arc_not_separates Brouwer.brouwerFPT e.symm

theorem exists_complementary_domains
    {r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2)}
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      IsBounded U ∧ ¬ IsBounded V ∧
      Disjoint U V ∧ U ∪ V = (range r)ᶜ ∧
      frontier U = range r ∧ frontier V = range r ∧
      IsCompact (closure U) := by
  obtain ⟨x, hx, hxb⟩ := step_A_exists_bounded Brouwer.brouwerFPT hcont hinj
  obtain ⟨y, hy, hyu⟩ := exists_unbounded_component r hcont
  let U := connectedComponentIn (range r)ᶜ x
  let V := connectedComponentIn (range r)ᶜ y
  have hne : U ≠ V := by
    intro h
    apply hyu
    change IsBounded V
    rw [← h]
    exact hxb
  refine ⟨U, V, isOpen_component r hcont x, isOpen_component r hcont y,
    isPathConnected_component r hcont hx, isPathConnected_component r hcont hy,
    hxb, hyu, ?_, ?_, ?_, ?_, hxb.isCompact_closure⟩
  · refine disjoint_left.mpr fun z hzU hzV => hne ?_
    exact (connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzV).symm
  · apply Subset.antisymm
    · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
    · intro z hz
      by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z)
      · left
        have heq := step_B_bounded_unique Brouwer.brouwerFPT hcont hinj z hz x hx hzb hxb
        change z ∈ connectedComponentIn (range r)ᶜ x
        rw [← heq]
        exact mem_connectedComponentIn hz
      · right
        have heq := unbounded_component_unique r hcont hzb hyu
        change z ∈ connectedComponentIn (range r)ᶜ y
        rw [← heq]
        exact mem_connectedComponentIn hz
  · exact component_boundary_eq Brouwer.brouwerFPT hcont hinj hx ⟨y, hy, hne.symm⟩
  · exact component_boundary_eq Brouwer.brouwerFPT hcont hinj hy ⟨x, hx, hne⟩

end Poincare.Topology.Plane.Jordan
