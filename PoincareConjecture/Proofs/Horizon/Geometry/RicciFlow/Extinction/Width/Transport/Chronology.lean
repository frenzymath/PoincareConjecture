import PoincareConjecture.Definitions.M67
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

noncomputable def repairedComponentPathChronology
    {g₀ : StandardInitialMetric}
    {F : SurgeryFlowData.{u}}
    {T : ℝ}
    {W : RepairedEventChildWitness F}
    (P : RepairedComponentPath F T W) :
    M67FiniteChronology (↑P.surgery_times : Set ℝ) 0 T := by
  classical
  let E : Finset ℝ := P.surgery_times.filter (fun x => x ∈ Set.Ioo (0 : ℝ) T)
  let L : List ℝ := E.sort
  let n : ℕ := E.card
  have hlen : L.length = n := by
    simpa [L, n] using
      (Finset.length_sort (s := E) (r := fun a b : ℝ => a ≤ b))
  have hmem (x : ℝ) : x ∈ L ↔ x ∈ E := by
    simpa [L] using
      (Finset.mem_sort (s := E) (r := fun a b : ℝ => a ≤ b) (a := x))
  refine
    { count := n
      time := fun i => L.get ⟨i.1, by simpa [hlen] using i.2⟩
      strict_mono := by
        intro i j hij
        let ii : Fin L.length := ⟨i.1, by simpa [hlen] using i.2⟩
        let jj : Fin L.length := ⟨j.1, by simpa [hlen] using j.2⟩
        have hij' : ii < jj := hij
        exact (Finset.sortedLT_sort E) hij'
      in_interval := by
        intro i
        have hi : L.get ⟨i.1, by simpa [hlen] using i.2⟩ ∈ L :=
          List.get_mem L ⟨i.1, by simpa [hlen] using i.2⟩
        have hiE : L.get ⟨i.1, by simpa [hlen] using i.2⟩ ∈ E :=
          (hmem _).mp hi
        exact (Finset.mem_filter.mp hiE).2
      complete := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          have hi : L.get ⟨i.1, by simpa [hlen] using i.2⟩ ∈ L :=
            List.get_mem L ⟨i.1, by simpa [hlen] using i.2⟩
          have hiE := (hmem _).mp hi
          have hxi : L.get ⟨i.1, by simpa [hlen] using i.2⟩ ∈
              (↑P.surgery_times : Set ℝ) := by
            exact (Finset.mem_filter.mp hiE).1
          have hinterval : L.get ⟨i.1, by simpa [hlen] using i.2⟩ ∈
              Set.Ioo (0 : ℝ) T := (Finset.mem_filter.mp hiE).2
          exact ⟨hxi, hinterval⟩
        · intro hx
          have hxE : x ∈ E := Finset.mem_filter.mpr ⟨hx.1, hx.2⟩
          have hxL : x ∈ L := (hmem _).mpr hxE
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxL
          refine ⟨⟨i, by simpa [hlen] using i.isLt⟩, ?_⟩
          exact hi }

end PoincareConjecture
