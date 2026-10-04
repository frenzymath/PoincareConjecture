import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexStars
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Homotopy.Equiv

/-!
# Coordinate neighborhoods of induced order subcomplexes

The open set where a selected group of coordinates has positive total
weight retracts by deleting the other coordinates and renormalizing.
Its straight-line homotopy preserves the original chain support. These
neighborhoods provide the geometric Mayer-Vietoris step for the actual
characteristic-simplex comparison.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators unitInterval

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]

/-- The total coordinate weight on the chosen vertices.
Source: the simplicial neighborhood construction in Hatcher, 2.27. -/
def orderComplexRestrictionWeight (s : Finset J) (z : J → ℝ) : ℝ :=
  ∑ i ∈ s, z i

/-- The open coordinate neighborhood of the induced subcomplex.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def orderComplexNeighborhood (s : Finset J) : Set (finiteOrderComplex J).space :=
  {z | 0 < orderComplexRestrictionWeight s z.val}

/-- The coordinate neighborhood is open in the actual realization.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem isOpen_orderComplexNeighborhood (s : Finset J) :
    IsOpen (orderComplexNeighborhood s) := by
  apply isOpen_lt continuous_const
  exact continuous_finsetSum s (fun i _ =>
    (continuous_apply i).comp continuous_subtype_val)

open scoped Classical in
/-- Delete the unselected coordinates and normalize the selected ones.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def orderComplexRestrictionCoord (s : Finset J) (z : J → ℝ) (i : J) : ℝ :=
  if i ∈ s then z i / orderComplexRestrictionWeight s z else 0

omit [PartialOrder J] [Fintype J] in
/-- Normalization makes the total selected weight equal to one.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexRestrictionCoord_weight (s : Finset J) (z : J → ℝ)
    (hz : orderComplexRestrictionWeight s z ≠ 0) :
    orderComplexRestrictionWeight s (orderComplexRestrictionCoord s z) = 1 := by
  classical
  simp only [orderComplexRestrictionWeight, orderComplexRestrictionCoord,
    Finset.sum_ite_mem, Finset.inter_self]
  rw [← Finset.sum_div]
  exact div_self hz

/-- Renormalization stays in the geometric order complex because its
support is contained in the original support. Source: Hatcher, 2.27. -/
theorem orderComplexRestrictionCoord_mem (s : Finset J)
    (z : orderComplexNeighborhood s) :
    orderComplexRestrictionCoord s z.val.val ∈ (finiteOrderComplex J).space := by
  classical
  have hz := (finiteOrderComplex_space J z.val.val).mp z.val.property
  have hpos : 0 < orderComplexRestrictionWeight s z.val.val := z.property
  apply (finiteOrderComplex_space J _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [orderComplexRestrictionCoord]
    split_ifs
    · exact div_nonneg (hz.1 i) hpos.le
    · exact le_rfl
  · simp only [orderComplexRestrictionCoord, Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)
  · intro i j hi hj
    apply hz.2.2 i j
    · intro h
      simp only [orderComplexRestrictionCoord, h, zero_div, ite_self] at hi
      exact hi rfl
    · intro h
      simp only [orderComplexRestrictionCoord, h, zero_div, ite_self] at hj
      exact hj rfl

/-- The renormalization is continuous on its positive-weight domain.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem continuous_orderComplexRestrictionCoord (s : Finset J) :
    Continuous (fun z : orderComplexNeighborhood s =>
      orderComplexRestrictionCoord s z.val.val) := by
  classical
  apply continuous_pi
  intro i
  dsimp only [orderComplexRestrictionCoord]
  split_ifs
  · exact ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val)).div
      (continuous_finsetSum s (fun j _ => (continuous_apply j).comp
        (continuous_subtype_val.comp continuous_subtype_val)))
      (fun z => ne_of_gt z.property)
  · exact continuous_const

/-- The actual continuous neighborhood retraction, still valued in the
neighborhood. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def orderComplexRestriction (s : Finset J) :
    C(orderComplexNeighborhood s, orderComplexNeighborhood s) := by
  classical
  refine ⟨fun z => ⟨⟨orderComplexRestrictionCoord s z.val.val,
    orderComplexRestrictionCoord_mem s z⟩, ?_⟩, ?_⟩
  · change 0 < orderComplexRestrictionWeight s (orderComplexRestrictionCoord s z.val.val)
    rw [orderComplexRestrictionCoord_weight s _ (ne_of_gt z.property)]
    exact zero_lt_one
  · exact ((continuous_orderComplexRestrictionCoord s).subtype_mk _).subtype_mk _

/-- A point already supported on the selected vertices has weight one.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexRestrictionWeight_eq_one (s : Finset J)
    (z : (finiteOrderComplex J).space) (hz : ∀ i ∉ s, z.val i = 0) :
    orderComplexRestrictionWeight s z.val = 1 := by
  classical
  rw [orderComplexRestrictionWeight,
    Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hz i hi)]
  exact ((finiteOrderComplex_space J z.val).mp z.property).2.1

/-- Renormalization fixes every point of the induced subcomplex.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexRestrictionCoord_eq_self (s : Finset J)
    (z : (finiteOrderComplex J).space) (hz : ∀ i ∉ s, z.val i = 0) :
    orderComplexRestrictionCoord s z.val = z.val := by
  classical
  funext i
  simp only [orderComplexRestrictionCoord, orderComplexRestrictionWeight_eq_one s z hz,
    div_one]
  split_ifs with hi
  · rfl
  · exact (hz i hi).symm

/-- The segment to the coordinate retraction stays in the open
neighborhood and preserves the original chain support.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexRestrictionSegment_mem (s : Finset J)
    (z : orderComplexNeighborhood s) (t : I) :
    (fun i => (1 - (t : ℝ)) * z.val.val i +
      (t : ℝ) * orderComplexRestrictionCoord s z.val.val i) ∈
        (finiteOrderComplex J).space ∧
    0 < orderComplexRestrictionWeight s (fun i => (1 - (t : ℝ)) * z.val.val i +
      (t : ℝ) * orderComplexRestrictionCoord s z.val.val i) := by
  classical
  let r := orderComplexRestrictionCoord s z.val.val
  have hz := (finiteOrderComplex_space J z.val.val).mp z.val.property
  have hr := (finiteOrderComplex_space J r).mp (orderComplexRestrictionCoord_mem s z)
  have hsupp (i : J) (hi : (1 - (t : ℝ)) * z.val.val i + (t : ℝ) * r i ≠ 0) :
      z.val.val i ≠ 0 := by
    intro h
    have hri : r i = 0 := by
      simp only [r, orderComplexRestrictionCoord, h, zero_div, ite_self]
    simp only [h, hri, mul_zero, add_zero] at hi
    exact hi rfl
  constructor
  · apply (finiteOrderComplex_space J _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (hz.1 i))
        (mul_nonneg t.property.1 (hr.1 i))
    · change (∑ i : J, ((1 - (t : ℝ)) * z.val.val i + (t : ℝ) * r i)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hz.2.1, hr.2.1]
      ring
    · intro i j hi hj
      exact hz.2.2 i j (hsupp i hi) (hsupp j hj)
  · change 0 < ∑ i ∈ s, ((1 - (t : ℝ)) * z.val.val i + (t : ℝ) * r i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      show (∑ i ∈ s, r i) = 1 from
        orderComplexRestrictionCoord_weight s _ (ne_of_gt z.property), mul_one]
    rcases lt_or_eq_of_le t.property.2 with ht | ht
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) z.property) t.property.1
    · rw [ht]
      norm_num

/-- The explicit deformation from the identity to coordinate
renormalization. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def orderComplexRestrictionHomotopy (s : Finset J) :
    (ContinuousMap.id (orderComplexNeighborhood s)).Homotopy (orderComplexRestriction s) where
  toFun q := ⟨⟨fun i => (1 - (q.1 : ℝ)) * q.2.val.val i +
    (q.1 : ℝ) * orderComplexRestrictionCoord s q.2.val.val i,
    (orderComplexRestrictionSegment_mem s q.2 q.1).1⟩,
    (orderComplexRestrictionSegment_mem s q.2 q.1).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul ((continuous_apply i).comp
        ((continuous_orderComplexRestrictionCoord s).comp continuous_snd)))
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (0 : ℝ)) * z.val.val i +
      0 * orderComplexRestrictionCoord s z.val.val i = z.val.val i
    ring
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (1 : ℝ)) * z.val.val i +
      1 * orderComplexRestrictionCoord s z.val.val i =
        orderComplexRestrictionCoord s z.val.val i
    ring

/-- The deformation fixes the induced subcomplex pointwise, which is
the condition needed when lifting it through a covering.
Source: Hatcher, Proposition 1.30 and Theorem 2.27. -/
theorem orderComplexRestrictionHomotopy_fixed (s : Finset J)
    (z : orderComplexNeighborhood s) (hz : ∀ i ∉ s, z.val.val i = 0) (t : I) :
    orderComplexRestrictionHomotopy s (t, z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change (fun i => (1 - (t : ℝ)) * z.val.val i +
    (t : ℝ) * orderComplexRestrictionCoord s z.val.val i) = z.val.val
  rw [orderComplexRestrictionCoord_eq_self s z.val hz]
  funext i
  ring

end PoincareMT.Proofs.M59
