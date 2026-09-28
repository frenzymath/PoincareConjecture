import PoincareConjecture.Definitions.M56Ancestry











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




theorem m56LiteralPathCover
    {F : SurgeryFlowData.{u}} {W : RepairedEventChildWitness F}
    (ancestry : RepairedFiniteAncestryData F W)
    (T : ℝ) (hT : T ∈ F.time_domain) :
    ∃ n : ℕ, ∃ points : Fin n → (F.slice T).carrier,
      ∀ x : (F.slice T).carrier, ∃ i : Fin n,
        x ∈ Set.range ((ancestry.path_for T hT (points i)).component
          ⟨T, F.time_domain_nonnegative hT, le_rfl⟩).inclusion := by
  obtain ⟨n, paths, hcover⟩ := ancestry.finite_path_cover T hT
  let terminal : Set.Icc (0 : ℝ) T :=
    ⟨T, F.time_domain_nonnegative hT, le_rfl⟩
  let points : Fin n → (F.slice T).carrier := fun i =>
    ((paths i).component terminal).inclusion
      ((paths i).component terminal).basepoint
  refine ⟨n, points, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨i, ?_⟩
  let selected := (ancestry.path_for T hT (points i)).component terminal
  have hpoint : points i ∈ connectedComponent
      (selected.inclusion selected.basepoint) := by
    rw [← selected.range_eq_component]
    exact ancestry.path_for_terminal_cover T hT (points i)
  have hrange : Set.range ((paths i).component terminal).inclusion =
      Set.range selected.inclusion := by
    rw [((paths i).component terminal).range_eq_component,
      selected.range_eq_component]
    exact (connectedComponent_eq hpoint).symm
  exact hrange ▸ hi


set_option linter.style.haveILetI false in










theorem finiteFreeProductCyclic_of_subsingleton
    {G : Type u} [Group G] (hG : Subsingleton G) :
    IsFiniteFreeProductCyclic G := by
  let F : FiniteOrCyclicFactors 0 :=
    { carrier := fun _ => G
      group := fun i => Fin.elim0 i
      kind := fun i => Fin.elim0 i }
  letI : ∀ i, Group (F.carrier i) := F.group
  let H := Monoid.CoprodI F.carrier
  have hH : Subsingleton H := by
    constructor
    intro a b
    have ha : a = 1 := by
      induction a using Monoid.CoprodI.induction_on with
      | one => rfl
      | of i x => exact Fin.elim0 i
      | mul x y hx hy => rw [hx, hy, one_mul]
    have hb : b = 1 := by
      induction b using Monoid.CoprodI.induction_on with
      | one => rfl
      | of i x => exact Fin.elim0 i
      | mul x y hx hy => rw [hx, hy, one_mul]
    exact ha.trans hb.symm
  let hom : G →* H :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := by intros; simp }
  have hbijective : Function.Bijective hom := by
    constructor
    · intro a b _
      exact hG.elim a b
    · intro y
      have hy : y = 1 := hH.elim y 1
      exact ⟨1, hy.symm⟩
  refine ⟨0, F, ?_⟩
  exact ⟨MulEquiv.ofBijective hom hbijective⟩




theorem finiteFreeProductCyclic_of_simplyConnected
    {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M] :
    ∀ x : M, IsFiniteFreeProductCyclic (FundamentalGroup M x) := by
  intro x
  exact finiteFreeProductCyclic_of_subsingleton
    (inferInstance : Subsingleton (FundamentalGroup M x))

end PoincareConjecture
