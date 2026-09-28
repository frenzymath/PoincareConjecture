import PoincareConjecture.Proofs.M76.Mathlib.PlanarCrossingContribution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Set Filter PlanarSegment
open scoped Topology BigOperators

namespace Polygon

variable {n : ℕ}

def HasNonverticalEdges (P : Polygon (ℝ × ℝ) n) : Prop :=
  ∀ i, (P i).1 ≠ (P (finRotate n i)).1

noncomputable def crossingIndex (P : Polygon (ℝ × ℝ) n) (q : ℝ × ℝ) : ℤ :=
  ∑ i, crossingContribution (P i) (P (finRotate n i)) q

private theorem sum_by_parts {I : Type*} [Fintype I] (r : Equiv.Perm I)
    (H C : I → ℤ) :
    (∑ i, (H i - H (r i)) * C i) = ∑ i, H i * (C i - C (r.symm i)) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    Equiv.sum_comp r (fun i => H i * C (r.symm i))

theorem eventuallyEq_crossingIndex (P : Polygon (ℝ × ℝ) n)
    (hP : P.HasNonverticalEdges) {q : ℝ × ℝ} (hq : q ∉ P.boundary ℝ) :
    ∀ᶠ z in 𝓝 q, P.crossingIndex z = P.crossingIndex q := by
  let r := finRotate n
  let H (i : Fin n) (z : ℝ × ℝ) := horizontalStep (P i).1 z
  let C (i : Fin n) := aboveLine (P i) (P (r i)) q
  have hedges (i : Fin n) : ∀ᶠ z in 𝓝 q,
      crossingContribution (P i) (P (r i)) z = (H i z - H (r i) z) * C i := by
    apply eventually_crossingContribution (hP i)
    intro h
    apply hq
    exact mem_iUnion.mpr ⟨i, by simpa only [edgeSet, affineSegment_eq_segment] using h⟩
  have hvertices (i : Fin n) : ∀ᶠ z in 𝓝 q,
      H i z * (C i - C (r.symm i)) = H i q * (C i - C (r.symm i)) := by
    by_cases hi : q.1 = (P i).1
    · have hprev : (P (r.symm i)).1 ≠ (P i).1 := by
        simpa only [r, Equiv.apply_symm_apply] using hP (r.symm i)
      have hc : C i = C (r.symm i) := by
        simp only [C, aboveLine, Equiv.apply_symm_apply, hi, height_left,
          height_right hprev]
      exact Eventually.of_forall fun z => by rw [hc, sub_self, mul_zero, mul_zero]
    · filter_upwards [eventuallyEq_horizontalStep hi] with z hz
      rw [show H i z = H i q from hz]
  filter_upwards [Filter.eventually_all.mpr hedges,
    Filter.eventually_all.mpr hvertices] with z hz hv
  calc
    P.crossingIndex z = ∑ i, (H i z - H (r i) z) * C i :=
      Finset.sum_congr rfl fun i _ => hz i
    _ = ∑ i, H i z * (C i - C (r.symm i)) := sum_by_parts r _ C
    _ = ∑ i, H i q * (C i - C (r.symm i)) := Finset.sum_congr rfl fun i _ => hv i
    _ = P.crossingIndex q := (sum_by_parts r _ C).symm

theorem isLocallyConstant_crossingIndex (P : Polygon (ℝ × ℝ) n)
    (hP : P.HasNonverticalEdges) :
    IsLocallyConstant (fun q : ↥((P.boundary ℝ)ᶜ) => P.crossingIndex q.val) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro q
  exact continuous_subtype_val.continuousAt.eventually
    (P.eventuallyEq_crossingIndex hP q.property)

theorem crossingIndex_eq_of_isPreconnected (P : Polygon (ℝ × ℝ) n)
    (hP : P.HasNonverticalEdges) {s : Set ↥((P.boundary ℝ)ᶜ)}
    (hs : IsPreconnected s) {q z : ↥((P.boundary ℝ)ᶜ)} (hq : q ∈ s) (hz : z ∈ s) :
    P.crossingIndex q.val = P.crossingIndex z.val :=
  (P.isLocallyConstant_crossingIndex hP).apply_eq_of_isPreconnected hs hq hz

end Polygon
