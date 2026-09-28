import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.OppositeCoordinate
import Mathlib.Data.Finset.Max











set_option autoImplicit false

namespace Poincare.Manifold.Schoenflies.Plane



theorem exists_lexicographic_min {ι A B : Type*} [Finite ι] [Nonempty ι]
    [LinearOrder A] [LinearOrder B] (f : ι → A × B) :
    ∃ i, (∀ j, (f i).1 ≤ (f j).1) ∧
      ∀ j, (f j).1 = (f i).1 → (f i).2 ≤ (f j).2 := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_min_image Finset.univ (fun j => (f j).1) Finset.univ_nonempty
  let s := Finset.univ.filter fun j => (f j).1 = (f a).1
  have hs : s.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun j => (f j).2) hs
  have hi1 : (f i).1 = (f a).1 := (Finset.mem_filter.mp hi).2
  refine ⟨i, ?_, ?_⟩
  · intro j
    rw [hi1]
    exact ha j (Finset.mem_univ j)
  · intro j hj
    exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.trans hi1⟩)



theorem linearIndependent_of_lex_nonnegative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : E ≃L[ℝ] (ℝ × ℝ)) {u v : E}
    (hnot : ¬ SameRay ℝ u v) (hu1 : 0 ≤ (e u).1) (hv1 : 0 ≤ (e v).1)
    (hu2 : (e u).1 = 0 → 0 ≤ (e u).2) (hv2 : (e v).1 = 0 → 0 ≤ (e v).2) :
    LinearIndependent ℝ ![u, v] := by
  have hu : u ≠ 0 := by rintro rfl; exact hnot (SameRay.zero_left v)
  have hv : v ≠ 0 := by rintro rfl; exact hnot (SameRay.zero_right u)
  by_contra hli
  have hs : SameRay ℝ u (-v) :=
    (sameRay_or_sameRay_neg_iff_not_linearIndependent.mpr hli).resolve_left hnot
  obtain ⟨r, hr, hru⟩ := hs.exists_pos_left hu (neg_ne_zero.mpr hv)
  have he : r • e u = -e v := by simpa only [map_smul, map_neg] using congrArg e hru
  have hfst : r * (e u).1 = -(e v).1 := congrArg Prod.fst he
  have hsnd : r * (e u).2 = -(e v).2 := congrArg Prod.snd he
  have huf : (e u).1 = 0 := by nlinarith
  have hvf : (e v).1 = 0 := by nlinarith
  have hus : (e u).2 = 0 := by
    have := hu2 huf
    have := hv2 hvf
    nlinarith
  apply hu
  apply e.injective
  rw [map_zero]
  exact Prod.ext huf hus

end Poincare.Manifold.Schoenflies.Plane
