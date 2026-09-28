import PoincareConjecture.Proofs.M76.Mathlib.BasisEvaluation
import PoincareConjecture.Proofs.M76.Mathlib.RadialConvexHull

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Module.Basis

variable {ι E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def nonnegativeCone (b : Basis ι ℝ E) (s : Set ι) : ConvexCone ℝ E where
  carrier := {x | (∀ i, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i = 0}
  smul_mem' := by
    intro c hc x hx
    constructor
    · intro i
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using mul_nonneg hc.le (hx.1 i)
    · intro i hi
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hx.2 i hi, mul_zero]
  add_mem' := by
    intro x hx y hy
    constructor
    · intro i
      simpa only [map_add, Finsupp.add_apply] using add_nonneg (hx.1 i) (hy.1 i)
    · intro i hi
      simp only [map_add, Finsupp.add_apply, hx.2 i hi, hy.2 i hi, add_zero]

theorem mem_nonnegativeCone_iff (b : Basis ι ℝ E) (s : Set ι) (x : E) :
    x ∈ b.nonnegativeCone s ↔ (∀ i, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i = 0 := Iff.rfl

variable [Finite ι]

theorem nonnegativeCone_eq_hull (b : Basis ι ℝ E) (s : Set ι) :
    b.nonnegativeCone s = ConvexCone.hull ℝ (insert 0 (b '' s)) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    let C := ConvexCone.hull ℝ (insert (0 : E) (b '' s))
    have hzero : (0 : E) ∈ C := ConvexCone.subset_hull (mem_insert _ _)
    have hterm : ∀ i : ι, b.repr x i • b i ∈ C := by
      intro i
      by_cases hi : i ∈ s
      · rcases (hx.1 i).eq_or_lt with hc | hc
        · rw [← hc, zero_smul]
          exact hzero
        · exact C.smul_mem hc (ConvexCone.subset_hull (mem_insert_of_mem _ ⟨i, hi, rfl⟩))
      · rw [hx.2 i hi, zero_smul]
        exact hzero
    rw [← b.sum_repr x]
    exact Finset.sum_induction _ (fun y => y ∈ C) (fun _ _ hx hy => C.add_mem hx hy)
      hzero (fun i _ => hterm i)
  · apply ConvexCone.hull_min
    rintro x (rfl | hx)
    · constructor <;> simp
    · obtain ⟨i, hi, rfl⟩ := hx
      constructor
      · intro j
        simp only [repr_self_apply]
        split_ifs <;> norm_num
      · intro j hj
        have hij : i ≠ j := fun he => hj (he ▸ hi)
        simp only [repr_self_apply, if_neg hij]

theorem isClosed_nonnegativeCone (b : Basis ι ℝ E) (s : Set ι) :
    IsClosed (b.nonnegativeCone s : Set E) := by
  classical
  let := Fintype.ofFinite ι
  have hc : ∀ i, Continuous (fun x : E => b.repr x i) :=
    fun i => (continuous_apply i).comp b.equivFunL.continuous
  change IsClosed {x : E | (∀ i, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i = 0}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter (fun i => isClosed_le (continuous_const (y := (0 : ℝ)))
    (hc i))).inter (isClosed_iInter (fun i =>
      isClosed_iInter (fun _ : i ∉ s =>
        isClosed_eq (hc i) (continuous_const (y := (0 : ℝ))))))

theorem exists_pos_smul_mem_simplex_of_mem_nonnegativeCone (b : Basis ι ℝ E)
    {s : Set ι} {x : E} (hx : x ∈ b.nonnegativeCone s) :
    ∃ r : ℝ, 0 < r ∧ ∃ y ∈ convexHull ℝ (insert 0 (b '' s)), r • y = x := by
  rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull] at hx
  exact (ConvexCone.mem_hull_of_convex (convex_convexHull ℝ _)).mp hx

end Module.Basis
