import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Equation
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Resolution

noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem isCompact_outerOval : IsCompact outerOval :=
  (isCompact_Icc.image (continuous_levelArc 1)).union
    (isCompact_Icc.image (continuous_levelArc (-1)))

theorem isCompact_innerOval : IsCompact innerOval :=
  (isCompact_Icc.image (continuous_levelArc 1)).union
    (isCompact_Icc.image (continuous_levelArc (-1)))

theorem isConnected_outerOval : IsConnected outerOval := by
  have hab : lowerRoot ≤ (3 / 5 : Real) := le_of_lt
    (lowerRoot_bounds.2.trans (by norm_num))
  apply ((isConnected_Icc hab).image _ (continuous_levelArc 1).continuousOn).union
    ?_ ((isConnected_Icc hab).image _ (continuous_levelArc (-1)).continuousOn)
  exact ⟨levelArc 1 lowerRoot, ⟨lowerRoot, ⟨le_rfl, hab⟩, rfl⟩,
    ⟨lowerRoot, ⟨le_rfl, hab⟩, levelArc_eq_of_radicand_zero levelRadicand_lowerRoot (-1) 1⟩⟩

theorem isConnected_innerOval : IsConnected innerOval := by
  have hab : upperRoot ≤ (1 : Real) := upperRoot_bounds.2.le
  apply ((isConnected_Icc hab).image _ (continuous_levelArc 1).continuousOn).union
    ?_ ((isConnected_Icc hab).image _ (continuous_levelArc (-1)).continuousOn)
  exact ⟨levelArc 1 upperRoot, ⟨upperRoot, ⟨le_rfl, hab⟩, rfl⟩,
    ⟨upperRoot, ⟨le_rfl, hab⟩, levelArc_eq_of_radicand_zero levelRadicand_upperRoot (-1) 1⟩⟩

theorem sourceHeight_mem_of_mem_outerOval {q : E2} (hq : q ∈ outerOval) :
    sourceHeight q ∈ Icc lowerRoot (3 / 5) := by
  rcases hq with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
  · rwa [sourceHeight_levelArc (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inl hz))]
  · rwa [sourceHeight_levelArc (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inl hz))]

theorem sourceHeight_mem_of_mem_innerOval {q : E2} (hq : q ∈ innerOval) :
    sourceHeight q ∈ Icc upperRoot 1 := by
  rcases hq with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
  · rwa [sourceHeight_levelArc (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inr hz))]
  · rwa [sourceHeight_levelArc (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inr hz))]

theorem norm_ge_of_mem_outerOval {q : E2} (hq : q ∈ outerOval) : (4 / 5 : Real) ≤ ‖q‖ := by
  have hz := sourceHeight_mem_of_mem_outerOval hq
  have hl := lowerRoot_bounds.1
  have he := (mem_levelSet_iff q).mp (levelSet_eq_outerOval_union_innerOval ▸ Or.inl hq)
  have hprod : 0 ≤ ((3 / 5 : Real) - sourceHeight q) *
      ((3 / 5 : Real) + sourceHeight q) := mul_nonneg (by linarith [hz.2]) (by linarith [hz.1])
  nlinarith [norm_nonneg q]

theorem norm_lt_of_mem_innerOval {q : E2} (hq : q ∈ innerOval) : ‖q‖ < (4 / 5 : Real) := by
  have hz := sourceHeight_mem_of_mem_innerOval hq
  have hl := upperRoot_bounds.1
  have he := (mem_levelSet_iff q).mp (levelSet_eq_outerOval_union_innerOval ▸ Or.inr hq)
  nlinarith [hz.1, sq_nonneg (sourceHeight q - 3 / 5), norm_nonneg q]

theorem disjoint_outerOval_innerOval : Disjoint outerOval innerOval := by
  apply disjoint_left.mpr
  intro q ho hi
  exact (not_lt_of_ge (norm_ge_of_mem_outerOval ho)) (norm_lt_of_mem_innerOval hi)

private def oval (i : Fin 2) : Set E2 := ![outerOval, innerOval] i

private theorem oval_closed (i : Fin 2) : IsClosed (oval i) := by
  fin_cases i
  · exact isCompact_outerOval.isClosed
  · exact isCompact_innerOval.isClosed

private theorem oval_connected (i : Fin 2) : IsConnected (oval i) := by
  fin_cases i
  · exact isConnected_outerOval
  · exact isConnected_innerOval

private theorem oval_disjoint : Pairwise (fun i j => Disjoint (oval i) (oval j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact disjoint_outerOval_innerOval
  · exact disjoint_outerOval_innerOval.symm
  · exact (hij rfl).elim

private theorem oval_cover : (⋃ i, oval i) = levelSet := by
  rw [levelSet_eq_outerOval_union_innerOval]
  ext q
  simp [oval, Fin.exists_fin_two]

theorem connectedComponentIn_levelSet_of_mem_outerOval {q : E2} (hq : q ∈ outerOval) :
    connectedComponentIn levelSet q = outerOval :=
  Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover oval oval_closed
    (fun i => (oval_connected i).isPreconnected) oval_disjoint oval_cover (i := 0) hq

theorem connectedComponentIn_levelSet_of_mem_innerOval {q : E2} (hq : q ∈ innerOval) :
    connectedComponentIn levelSet q = innerOval :=
  Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover oval oval_closed
    (fun i => (oval_connected i).isPreconnected) oval_disjoint oval_cover (i := 1) hq

theorem card_connectedComponents_levelSet : Nat.card (ConnectedComponents levelSet) = 2 := by
  simpa using Poincare.Topology.card_connectedComponents_of_finite_closed_cover oval
    oval_closed oval_connected oval_disjoint oval_cover

end Poincare.Manifold.Schoenflies.Saddle.Nested
