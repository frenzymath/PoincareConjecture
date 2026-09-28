import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.GenericFrame
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Ray
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

theorem exists_linearMap_neg_pos_of_not_sameRay {E : Type*}
    [AddCommGroup E] [Module ℝ E] {u v : E} (hnot : ¬ SameRay ℝ u v) :
    ∃ X : E →ₗ[ℝ] ℝ, X u < 0 ∧ 0 < X v := by
  classical
  have hu : u ≠ 0 := by rintro rfl; exact hnot (SameRay.zero_left v)
  have hv : v ≠ 0 := by rintro rfl; exact hnot (SameRay.zero_right u)
  by_cases hli : LinearIndependent ℝ ![u, v]
  · have hneg : LinearIndependent ℝ ![-u, v] := by
      apply linearIndependent_fin2.mpr
      refine ⟨hv, ?_⟩
      intro c hc
      change c • v = -u at hc
      apply (linearIndependent_fin2.mp hli).2 (-c)
      change (-c) • v = u
      rw [neg_smul, hc, neg_neg]
    obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hneg.linearIndepOn_univ
    have hfu : -f u = 1 := by simpa using hf 0 (mem_univ _)
    have hfv : f v = 1 := by simpa using hf 1 (mem_univ _)
    exact ⟨f, by linarith, by linarith⟩
  · have hopp : SameRay ℝ u (-v) :=
      (sameRay_or_sameRay_neg_iff_not_linearIndependent.mpr hli).resolve_left hnot
    obtain ⟨r, hr, hru⟩ := hopp.exists_pos_left hu (neg_ne_zero.mpr hv)
    obtain ⟨f, hfu⟩ := Module.Projective.exists_dual_eq_one ℝ hu
    have hrel := congrArg f hru
    simp only [map_smul, map_neg, hfu, smul_eq_mul, mul_one] at hrel
    refine ⟨-f, ?_, ?_⟩
    · change -f u < 0
      rw [hfu]
      exact neg_lt_zero.mpr zero_lt_one
    · change 0 < -f v
      linarith

theorem exists_continuousLinearEquiv_fst_neg_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {u v : E} (hnot : ¬ SameRay ℝ u v) :
    ∃ e : E ≃L[ℝ] (ℝ × ℝ), (e u).1 < 0 ∧ 0 < (e v).1 := by
  obtain ⟨X, hXu, hXv⟩ := exists_linearMap_neg_pos_of_not_sameRay hnot
  have hX : X ≠ 0 := by
    intro hz
    have hu := LinearMap.congr_fun hz u
    exact hXu.ne (by simpa using hu)
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_snd_eq hdim X hX
  refine ⟨e.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ), ?_, ?_⟩
  · change (e u).2 < 0
    rw [he]
    exact hXu
  · change 0 < (e v).2
    rw [he]
    exact hXv

theorem not_sameRay_sub_of_segments_inter_subset_singleton {E : Type*}
    [AddCommGroup E] [Module ℝ E] {q a b : E} (ha : a ≠ q) (hb : b ≠ q)
    (hinter : segment ℝ q a ∩ segment ℝ q b ⊆ {q}) :
    ¬ SameRay ℝ (a - q) (b - q) := by
  intro hs
  obtain ⟨r, hr, hru⟩ := hs.exists_pos_left (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)
  let t : ℝ := min 1 r / 2
  have hm : 0 < min (1 : ℝ) r := lt_min zero_lt_one hr
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by
    have := min_le_left (1 : ℝ) r
    dsimp [t]
    linarith
  have htr : t < r := by
    have := min_le_right (1 : ℝ) r
    dsimp [t]
    linarith
  let p := AffineMap.lineMap q a t
  have hpA : p ∈ segment ℝ q a := lineMap_mem_segment ℝ q a ⟨ht.le, ht1.le⟩
  have hpB : p ∈ segment ℝ q b := by
    have he : AffineMap.lineMap q b (t / r) = p := by
      dsimp [p]
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module',
        ← hru, smul_smul, div_mul_cancel₀ _ hr.ne']
    rw [← he]
    exact lineMap_mem_segment ℝ q b
      ⟨(div_pos ht hr).le, (div_le_one hr).mpr htr.le⟩
  have hpeq : p = q := hinter ⟨hpA, hpB⟩
  have hzero : t • (a - q) = 0 := by
    have heq := congrArg (fun z => z - q) hpeq
    simpa only [p, AffineMap.lineMap_apply_module', add_sub_cancel_right, sub_self] using heq
  exact ha (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne'))

end Poincare.Manifold.Schoenflies.Plane
