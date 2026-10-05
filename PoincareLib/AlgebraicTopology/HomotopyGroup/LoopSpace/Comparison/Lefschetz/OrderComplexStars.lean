import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology
import Mathlib.Analysis.Convex.Contractible

/-!
# Contractible vertex-star intersections in a finite order complex

The star of a vertex is the set where its barycentric coordinate is
positive. Every nonempty finite intersection contracts to the barycenter
of the prescribed vertices. These are actual subsets of the geometric
realization supplied by M02. Sources: Hatcher, Theorem 2.27, pp. 128-130,
and the subdivision argument in Theorem 2C.3, pp. 179-181.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]

/-- The common vertex star, as a subset of the coordinate ambient space.
Source: Hatcher's simplicial subdivision proof, Theorem 2C.3, pp. 179-181. -/
def orderComplexStar (s : Finset J) : Set (J → ℝ) :=
  {z | z ∈ (finiteOrderComplex J).space ∧ ∀ i ∈ s, 0 < z i}

/-- A nonempty common star can only prescribe a linearly ordered set of
vertices. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexStar_chain {s : Finset J} (h : (orderComplexStar s).Nonempty) :
    ∀ i ∈ s, ∀ j ∈ s, i ≤ j ∨ j ≤ i := by
  obtain ⟨z, hz, hpos⟩ := h
  intro i hi j hj
  exact ((finiteOrderComplex_space J z).mp hz).2.2 i j
    (ne_of_gt (hpos i hi)) (ne_of_gt (hpos j hj))

open scoped Classical in
/-- The equal-weight point on a nonempty prescribed chain belongs to
its common star. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexStar_barycenter_mem (s : Finset J) (hne : s.Nonempty)
    (hchain : ∀ i ∈ s, ∀ j ∈ s, i ≤ j ∨ j ≤ i) :
    (fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0) ∈ orderComplexStar s := by
  classical
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hne.card_pos
  constructor
  · apply (finiteOrderComplex_space J _).mpr
    refine ⟨fun i => ?_, ?_, ?_⟩
    · split_ifs
      · exact le_of_lt (inv_pos.mpr hcard)
      · exact le_rfl
    · simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hcard)
    · intro i j hi hj
      have his : i ∈ s := by by_contra h; simp [h] at hi
      have hjs : j ∈ s := by by_contra h; simp [h] at hj
      exact hchain i his j hjs
  · intro i hi
    simpa only [if_pos hi] using inv_pos.mpr hcard

/-- A common star is star-convex about every point supported exactly on
its prescribed vertices. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexStar_starConvex (s : Finset J) (c : J → ℝ)
    (hc : c ∈ orderComplexStar s) (hsupp : ∀ i ∉ s, c i = 0) :
    StarConvex ℝ c (orderComplexStar s) := by
  intro z hz a b ha hb hab
  have hc' := (finiteOrderComplex_space J c).mp hc.1
  have hz' := (finiteOrderComplex_space J z).mp hz.1
  have hsupport (i : J) (hi : (a • c + b • z) i ≠ 0) : z i ≠ 0 := by
    intro hzi
    have his : i ∉ s := fun his => (ne_of_gt (hz.2 i his)) hzi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsupp i his, hzi,
      mul_zero, add_zero] at hi
    exact hi rfl
  constructor
  · apply (finiteOrderComplex_space J _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg ha (hc'.1 i)) (mul_nonneg hb (hz'.1 i))
    · change (∑ i : J, (a * c i + b * z i)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hc'.2.1, hz'.2.1, mul_one, mul_one, hab]
    · intro i j hi hj
      exact hz'.2.2 i j (hsupport i hi) (hsupport j hj)
  · intro i hi
    change 0 < a * c i + b * z i
    have hci := hc.2 i hi
    have hzi := hz.2 i hi
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      simpa only [← ha0, hb1, zero_mul, one_mul, zero_add] using hzi
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hci) (mul_nonneg hb hzi.le)

/-- Every nonempty common star for a nonempty prescribed vertex set is
contractible. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexStar_contractible (s : Finset J) (hne : s.Nonempty)
    (h : (orderComplexStar s).Nonempty) : ContractibleSpace (orderComplexStar s) := by
  classical
  let c : J → ℝ := fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0
  have hc : c ∈ orderComplexStar s :=
    orderComplexStar_barycenter_mem s hne (orderComplexStar_chain h)
  exact (orderComplexStar_starConvex s c hc (by
    intro i hi
    simp only [c, if_neg hi])).contractibleSpace h

/-- The ambient common-star subtype is homeomorphic to the same open
intersection inside the realization. Source: Hatcher, Theorem 2.27,
pp. 128-130. -/
def orderComplexStarHomeomorph (s : Finset J) :
    orderComplexStar s ≃ₜ
      {z : (finiteOrderComplex J).space | ∀ i ∈ s, 0 < z.val i} where
  toFun z := ⟨⟨z.val, z.property.1⟩, z.property.2⟩
  invFun z := ⟨z.val.val, z.val.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Every nonempty intersection of the actual vertex-star cover is
contractible. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplex_vertexStarIntersection_contractible (s : Finset J)
    (hne : s.Nonempty)
    (h : Nonempty {z : (finiteOrderComplex J).space | ∀ i ∈ s, 0 < z.val i}) :
    ContractibleSpace {z : (finiteOrderComplex J).space | ∀ i ∈ s, 0 < z.val i} := by
  let e := orderComplexStarHomeomorph s
  have hs : (orderComplexStar s).Nonempty := by
    obtain ⟨z⟩ := h
    exact ⟨(e.symm z).val, (e.symm z).property⟩
  let := orderComplexStar_contractible s hne hs
  exact e.contractibleSpace_iff.mp inferInstance

/-- Vertex stars are open in the actual order-complex realization.
Source: Hatcher, Theorem 2C.3, pp. 179-181. -/
theorem isOpen_orderComplex_vertexStar (i : J) :
    IsOpen {z : (finiteOrderComplex J).space | 0 < z.val i} :=
  isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)

/-- The finitely many vertex stars cover the actual realization.
Source: Hatcher, Theorem 2C.3, pp. 179-181. -/
theorem orderComplex_vertexStars_cover (z : (finiteOrderComplex J).space) :
    ∃ i, 0 < z.val i := by
  have hz := (finiteOrderComplex_space J z.val).mp z.property
  by_contra! h
  have hzero (i : J) : z.val i = 0 := le_antisymm (h i) (hz.1 i)
  have hsum := hz.2.1
  simp only [hzero, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

end PoincareMT.Proofs.M59
