import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.Regularity
import Mathlib.Analysis.Calculus.MeanValue









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem roundedVertexPath_abs_eq_edge (P : ℤ → E) (i : ℤ) {t : ℝ}
    (ht : t ∈ Icc (i : ℝ) ((i : ℝ) + 1)) :
    roundedVertexPath abs P t = P i + (t - i) • (P (i + 1) - P i) := by
  let j : ℤ := ⌊t + 1 / 2⌋
  have hjlo : (j : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hjhi : t + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hji : i ≤ j := by
    have h : (i : ℝ) - 1 < j := by linarith [ht.1]
    have h' : i - 1 < j := by exact_mod_cast h
    omega
  have hij : j ≤ i + 1 := by
    have h : (j : ℝ) < i + 2 := by linarith [ht.2]
    have h' : j < i + 2 := by exact_mod_cast h
    omega
  change roundedCorner abs (P j) (P j - P (j - 1)) (P (j + 1) - P j) (t - j) = _
  rcases (show j = i ∨ j = i + 1 by omega) with rfl | hj
  · rw [roundedCorner, abs_of_nonneg (by linarith [ht.1])]
    module
  · rw [hj, roundedCorner, Int.cast_add, Int.cast_one,
      abs_of_nonpos (by linarith [ht.2])]
    simp only [add_sub_cancel_right]
    module

theorem dist_deletionClock_le {ρ : ℝ → ℝ} {δ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hδ : 0 ≤ δ) (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) (t : ℝ) :
    dist (deletionClock ρ N t) (deletionClock abs N t) ≤ δ / 4 := by
  let i : ℤ := ⌊t + 1 / 2⌋
  let u := deletionClockVertex N i - deletionClockVertex N (i - 1)
  let v := deletionClockVertex N (i + 1) - deletionClockVertex N i
  have hu : 1 / 2 ≤ u ∧ u ≤ 1 := by
    simpa only [u, sub_add_cancel] using deletionClockVertex_step_bounds hN (i - 1)
  have hv : 1 / 2 ≤ v ∧ v ≤ 1 := deletionClockVertex_step_bounds hN i
  have huv : |v - u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  have hf : 0 ≤ (ρ (t - i) - |t - i|) / 2 := by linarith [(hbound (t - i)).1]
  have hf' : (ρ (t - i) - |t - i|) / 2 ≤ δ / 2 := by linarith [(hbound (t - i)).2]
  have heq : deletionClock ρ N t - deletionClock abs N t =
      ((ρ (t - i) - |t - i|) / 2) * (v - u) := by
    simp only [deletionClock, roundedVertexPath, roundedCorner, smul_eq_mul, u, v, i]
    ring
  rw [Real.dist_eq, heq, abs_mul, abs_of_nonneg hf]
  calc
    _ ≤ (δ / 2) * (1 / 2) := mul_le_mul hf' huv (abs_nonneg _) (by linarith)
    _ = δ / 4 := by ring

theorem norm_deriv_roundedPolygonParameter_le {N : ℕ} [NeZero N] (p : Polygon E N)
    {ρ : ℝ → ℝ} {δ B : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1)
    (hB : ∀ i, ‖p i‖ ≤ B) (t : ℝ) :
    ‖deriv (roundedPolygonParameter ρ p) t‖ ≤ 2 * B := by
  let i : ℤ := ⌊t + 1 / 2⌋
  let P : ℤ → E := fun j => p (polygonIntegerIndex N j)
  have hilo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hihi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
    constructor <;> linarith
  change ‖deriv (roundedVertexPath ρ P) t‖ ≤ _
  rw [deriv_roundedVertexPath_eq_local _ hδ hδhalf htail hbound hρ i ht,
    (hasDerivAt_roundedCorner _ _ _ (hρ (t - i))).deriv]
  have hl : 0 ≤ (1 - deriv ρ (t - i)) / 2 := by linarith [(abs_le.mp (hder (t - i))).2]
  have hr : 0 ≤ (1 + deriv ρ (t - i)) / 2 := by linarith [(abs_le.mp (hder (t - i))).1]
  have hleft : ‖P i - P (i - 1)‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [hB (polygonIntegerIndex N i), hB (polygonIntegerIndex N (i - 1))])
  have hright : ‖P (i + 1) - P i‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [hB (polygonIntegerIndex N (i + 1)), hB (polygonIntegerIndex N i)])
  calc
    _ ≤ ‖((1 - deriv ρ (t - i)) / 2) • (P i - P (i - 1))‖ +
        ‖((1 + deriv ρ (t - i)) / 2) • (P (i + 1) - P i)‖ := norm_add_le _ _
    _ = (1 - deriv ρ (t - i)) / 2 * ‖P i - P (i - 1)‖ +
        (1 + deriv ρ (t - i)) / 2 * ‖P (i + 1) - P i‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hr]
    _ ≤ (1 - deriv ρ (t - i)) / 2 * (2 * B) +
        (1 + deriv ρ (t - i)) / 2 * (2 * B) :=
      add_le_add (mul_le_mul_of_nonneg_left hleft hl) (mul_le_mul_of_nonneg_left hright hr)
    _ = 2 * B := by ring

theorem polygonLinearParameter_eq_fin_edge {N : ℕ} [NeZero N] (p : Polygon E N)
    (i : Fin N) {t : ℝ} (ht : t ∈ Icc (i : ℝ) ((i : ℝ) + 1)) :
    polygonLinearParameter p t = p i + (t - i) • (p (finRotate N i) - p i) := by
  rw [polygonLinearParameter_eq_edge p (i : ℤ) (by exact_mod_cast ht), polygonIntegerIndex_nat]
  simp only [Int.cast_natCast, Polygon.edgePath, AffineMap.lineMap_apply_module']
  module

theorem polygonLinearParameter_delete_last_clock (p : Polygon E (n + 4))
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0)) {t : ℝ}
    (ht : t ∈ Icc 0 ((n + 4 : ℕ) : ℝ)) :
    polygonLinearParameter (polygonDeleteVertex p (Fin.last (n + 3)))
      (deletionClock abs (n + 4) t) = polygonLinearParameter p t := by
  let i : ℤ := min ⌊t⌋ (n + 3)
  have hfloor : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
  have hi : 0 ≤ i := le_min hfloor (by omega)
  have hin : i ≤ n + 3 := min_le_right _ _
  have hit : (i : ℝ) ≤ t := (Int.cast_le.mpr (min_le_left _ _)).trans (Int.floor_le _)
  have hti : t ≤ (i : ℝ) + 1 := by
    by_cases h : ⌊t⌋ ≤ n + 3
    · dsimp [i]
      rw [min_eq_left h]
      exact (Int.lt_floor_add_one t).le
    · have heq : i = n + 3 := min_eq_right (by omega)
      rw [heq]
      push_cast
      have := ht.2
      push_cast at this
      linarith
  have htedge : t ∈ Icc (i : ℝ) ((i : ℝ) + 1) := ⟨hit, hti⟩
  have hc := roundedVertexPath_abs_eq_edge (deletionClockVertex (n + 4)) i htedge
  change deletionClock abs (n + 4) t = _ at hc
  by_cases hret : i < n + 2
  · have hcl : deletionClock abs (n + 4) t = t := by
      rw [hc, deletionClockVertex_eq_self hi (by omega),
        deletionClockVertex_eq_self (by omega) (by omega)]
      simp only [Int.cast_add, Int.cast_one, smul_eq_mul]
      ring
    rw [hcl, polygonLinearParameter_eq_edge _ i htedge,
      polygonLinearParameter_eq_edge _ i htedge]
    simp only [Polygon.edgePath, AffineMap.lineMap_apply_module', ← polygonIntegerIndex_succ]
    rw [polygonDeleteVertex_last_integer p hi (by omega),
      polygonDeleteVertex_last_integer p (by omega) (by omega)]
  · have hq (s : ℝ) (hs : s ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) :
        polygonLinearParameter (polygonDeleteVertex p (Fin.last (n + 3))) s =
          p (Fin.last (n + 2)).castSucc + (s - ((n : ℝ) + 2)) •
            (p 0 - p (Fin.last (n + 2)).castSucc) := by
      rw [polygonLinearParameter_eq_fin_edge _ (Fin.last (n + 2)) (by
        simp only [Fin.val_last, Nat.cast_add, Nat.cast_ofNat]
        constructor <;> linarith [hs.1, hs.2]), finRotate_last]
      simp only [polygonDeleteVertex_last_apply, Fin.castSucc_zero, Fin.val_last,
        Nat.cast_add, Nat.cast_ofNat]
    rcases (show i = n + 2 ∨ i = n + 3 by omega) with hi2 | hi3
    · have hcl : deletionClock abs (n + 4) t = (n : ℝ) + 2 +
          (t - ((n : ℝ) + 2)) / 2 := by
        rw [hc, hi2, deletionClockVertex_eq_self (by omega) (by omega)]
        rw [show (n : ℤ) + 2 + 1 = (n + 4 : ℕ) - 1 by omega,
          deletionClockVertex_last (by omega)]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add,
          Nat.cast_ofNat, smul_eq_mul]
        ring
      have hct : deletionClock abs (n + 4) t ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3) := by
        rw [hcl]
        rw [hi2] at hit hti
        push_cast at hit hti
        constructor <;> linarith
      rw [hq _ hct, polygonLinearParameter_eq_fin_edge _ (Fin.last (n + 2)).castSucc (by
        simpa only [hi2, Fin.val_castSucc, Fin.val_last, Nat.cast_add,
          Nat.cast_ofNat, Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using htedge)]
      have hrotate : finRotate (n + 4) (Fin.last (n + 2)).castSucc = Fin.last (n + 3) := by
        exact finRotate_of_lt (by omega)
      rw [hrotate, hcl, hmid, midpoint_eq_smul_add, invOf_eq_inv]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_ofNat]
      module
    · have hcl : deletionClock abs (n + 4) t = (n : ℝ) + 5 / 2 +
          (t - ((n : ℝ) + 3)) / 2 := by
        rw [hc, hi3]
        rw [show (n : ℤ) + 3 = (n + 4 : ℕ) - 1 by omega,
          deletionClockVertex_last (by omega), sub_add_cancel]
        have hz : deletionClockVertex (n + 4) 0 = 0 := by
          simpa only [Int.cast_zero] using
            deletionClockVertex_eq_self (N := n + 4) (j := 0) (by omega) (by omega)
        have hNval : deletionClockVertex (n + 4) ((n + 4 : ℕ) : ℤ) = ((n + 4 : ℕ) : ℝ) - 1 := by
          simpa only [zero_add, hz] using deletionClockVertex_add_period (show 0 < n + 4 by omega) 0
        rw [hNval]
        simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_ofNat, Nat.cast_add,
          Nat.cast_ofNat, smul_eq_mul]
        ring
      have hct : deletionClock abs (n + 4) t ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3) := by
        rw [hcl]
        rw [hi3] at hit hti
        push_cast at hit hti
        constructor <;> linarith
      rw [hq _ hct, polygonLinearParameter_eq_fin_edge _ (Fin.last (n + 3)) (by
        simpa only [hi3, Fin.val_last, Nat.cast_add, Nat.cast_ofNat,
          Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using htedge), finRotate_last,
        hcl, hmid, midpoint_eq_smul_add, invOf_eq_inv]
      simp only [Fin.val_last, Nat.cast_add, Nat.cast_ofNat]
      module

theorem contDiff_roundedPolygonParameter_const {N : ℕ} [NeZero N] (p : Polygon E N)
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (roundedPolygonParameter ρ p) := by
  have hP (i : Fin N) : ContDiff ℝ ∞ (fun _ : ℝ => p i) := contDiff_const
  have hs : ContDiff ℝ ∞ (fun x : ℝ × ℝ => roundedPolygonParameter ρ p x.2) :=
    contDiff_roundedPolygonParameter (p := fun _ : ℝ => p) hδ hδhalf htail hbound hρ hP
  have hc := hs.comp (show ContDiff ℝ ∞ (fun t : ℝ => ((0 : ℝ), t)) from
    contDiff_const.prodMk contDiff_id)
  convert hc using 1
  rfl


theorem dist_roundedPolygon_delete_last_clock_le (p : Polygon E (n + 4))
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0))
    {ρ : ℝ → ℝ} {δ B : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1)
    (hB : ∀ i, ‖p i‖ ≤ B) {t : ℝ} (ht : t ∈ Icc 0 ((n + 4 : ℕ) : ℝ)) :
    dist (roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3)))
      (deletionClock ρ (n + 4) t)) (polygonLinearParameter p t) ≤ 3 * δ * B := by
  let q := polygonDeleteVertex p (Fin.last (n + 3))
  have hB0 : 0 ≤ B := (norm_nonneg (p 0)).trans (hB 0)
  have hBq (i : Fin (n + 3)) : ‖q i‖ ≤ B := by
    dsimp [q]
    rw [polygonDeleteVertex_last_apply]
    exact hB i.castSucc
  have hs := contDiff_roundedPolygonParameter_const q hδ hδhalf htail hbound hρ
  have hmove : dist (roundedPolygonParameter ρ q (deletionClock ρ (n + 4) t))
      (roundedPolygonParameter ρ q (deletionClock abs (n + 4) t)) ≤
        2 * B * dist (deletionClock ρ (n + 4) t) (deletionClock abs (n + 4) t) := by
    rw [dist_eq_norm, dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s _ => hs.differentiable (by simp) s)
      (fun s _ => norm_deriv_roundedPolygonParameter_le q hδ hδhalf htail hbound
        (hρ.differentiable (by simp)) hder hBq s)
      convex_univ (mem_univ _) (mem_univ _)
  have hmove' : dist (roundedPolygonParameter ρ q (deletionClock ρ (n + 4) t))
      (roundedPolygonParameter ρ q (deletionClock abs (n + 4) t)) ≤ 2 * B * (δ / 4) :=
    hmove.trans (mul_le_mul_of_nonneg_left
      (dist_deletionClock_le (by omega) hδ.le hbound t) (by positivity))
  have herr := dist_roundedPolygonParameter_le q hδ hδhalf htail hbound hBq
    (deletionClock abs (n + 4) t)
  have hlin := polygonLinearParameter_delete_last_clock p hmid ht
  change polygonLinearParameter q (deletionClock abs (n + 4) t) = _ at hlin
  rw [hlin] at herr
  have htri := dist_triangle
    (roundedPolygonParameter ρ q (deletionClock ρ (n + 4) t))
    (roundedPolygonParameter ρ q (deletionClock abs (n + 4) t)) (polygonLinearParameter p t)
  change dist (roundedPolygonParameter ρ q (deletionClock ρ (n + 4) t)) _ ≤ _
  nlinarith [mul_nonneg hδ.le hB0]

end Poincare.Manifold.Schoenflies.Plane
