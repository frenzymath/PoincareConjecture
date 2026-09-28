import PoincareConjecture.Proofs.M76.Mathlib.ReplacedSimplexCoordinates
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace AffineBasis

variable {ι E : Type*} [Finite ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_interior_union_convexHull_update (b : AffineBasis ι ℝ E) (i : ι) (q x : E)
    (hqi : b.coord i q < 0) (hxi : b.coord i x = 0)
    (hx : ∀ j, j ≠ i → 0 < b.coord j x) :
    x ∈ interior (convexHull ℝ (range b) ∪ convexHull ℝ (range (Function.update b i q))) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional
  let V : Set E := {y | ∀ j ∈ Finset.univ.erase i,
    0 < b.coord j y ∧ 0 < b.coord j y - (b.coord i y / b.coord i q) * b.coord j q}
  have hcoord (j : ι) : Continuous (b.coord j) := continuous_barycentric_coord b j
  have hV : IsOpen V := by
    have he : V = ⋂ j ∈ Finset.univ.erase i, {y |
        0 < b.coord j y ∧ 0 < b.coord j y - (b.coord i y / b.coord i q) * b.coord j q} := by
      ext y
      simp only [V, mem_ofPred_eq, mem_iInter]
    rw [he]
    exact isOpen_biInter_finset (fun j _ =>
      (isOpen_lt continuous_const (hcoord j)).inter
        (isOpen_lt continuous_const ((hcoord j).sub
          (((hcoord i).div_const _).mul_const _))))
  have hxV : x ∈ V := by
    intro j hj
    have hjpos := hx j (Finset.ne_of_mem_erase hj)
    simpa only [hxi, zero_div, zero_mul, sub_zero] using And.intro hjpos hjpos
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hV.mem_nhds hxV)
  intro y hy
  by_cases hiy : 0 ≤ b.coord i y
  · left
    rw [b.convexHull_eq_nonneg_coord]
    intro j
    by_cases hji : j = i
    · simpa only [hji] using hiy
    · exact (hy j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).1.le
  · right
    apply b.mem_convexHull_update_of_coord i q y hqi.ne
      (div_nonneg_of_nonpos (not_le.mp hiy).le hqi.le)
    intro j hji
    exact (hy j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).2.le

end AffineBasis
