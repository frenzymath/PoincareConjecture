import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.Clock
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedPolygon
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.DeleteVertex










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem polygonDeleteVertex_last_apply (p : Polygon E (n + 4)) (i : Fin (n + 3)) :
    polygonDeleteVertex p (Fin.last (n + 3)) i = p i.castSucc := by
  change p (cyclicArcIndex (finRotate (n + 4) (Fin.last (n + 3))) (n + 2) i) = _
  rw [finRotate_last]
  apply congrArg p
  have h := congrFun (finCycle_eq_finRotate_iterate (k := i.castSucc)) (0 : Fin (n + 4))
  simpa only [cyclicArcIndex, finCycle_apply, zero_add, Fin.val_castSucc] using h.symm

theorem polygonIntegerIndex_eq_mk {N : ℕ} [NeZero N] {j : ℤ}
    (hj : 0 ≤ j) (hjN : j < N) :
    polygonIntegerIndex N j = ⟨j.toNat, (Int.toNat_lt hj).mpr hjN⟩ := by
  apply Fin.ext
  simp only [polygonIntegerIndex, Int.emod_eq_of_lt hj hjN]

theorem polygonIntegerIndex_neg_one {N : ℕ} :
    polygonIntegerIndex (N + 1) (-1) = Fin.last N := by
  have h := polygonIntegerIndex_add_period (n := N + 1) (-1)
  rw [show (-1 : ℤ) + (N + 1 : ℕ) = N by omega] at h
  rw [← h]
  exact polygonIntegerIndex_nat (Fin.last N)

@[simp] theorem polygonIntegerIndex_zero {N : ℕ} [NeZero N] :
    polygonIntegerIndex N 0 = 0 := by
  simpa only [Fin.val_zero, Nat.cast_zero] using polygonIntegerIndex_nat (0 : Fin N)

@[simp] theorem polygonIntegerIndex_self {N : ℕ} [NeZero N] :
    polygonIntegerIndex N N = 0 := by
  simpa only [zero_add, polygonIntegerIndex_zero] using
    polygonIntegerIndex_add_period (n := N) 0

theorem polygonIntegerIndex_one {N : ℕ} (hN : 1 < N) :
    haveI : NeZero N := ⟨by omega⟩
    polygonIntegerIndex N 1 = ⟨1, hN⟩ := by
  let : NeZero N := ⟨by omega⟩
  simpa only [Nat.cast_one] using polygonIntegerIndex_nat (⟨1, hN⟩ : Fin N)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem polygonDeleteVertex_last_integer (p : Polygon E (n + 4)) {j : ℤ}
    (hj : 0 ≤ j) (hjn : j < n + 3) :
    (polygonDeleteVertex p (Fin.last (n + 3))) (polygonIntegerIndex (n + 3) j) =
      p (polygonIntegerIndex (n + 4) j) := by
  rw [polygonDeleteVertex_last_apply, polygonIntegerIndex_eq_mk hj hjn,
    polygonIntegerIndex_eq_mk hj (show j < n + 4 by omega)]
  rfl


theorem roundedPolygon_delete_last_eq_of_interior (p : Polygon E (n + 4))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    {i : ℤ} (hi : 1 ≤ i) (hin : i < n + 2) {t : ℝ}
    (ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ)) :
    roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3)))
        (deletionClock ρ (n + 4) t) = roundedPolygonParameter ρ p t := by
  rw [deletionClock_eq_self hδ hδhalf htail hbound hi (by omega) ht]
  change roundedVertexPath ρ _ t = roundedVertexPath ρ _ t
  rw [roundedVertexPath_eq_local _ hδ hδhalf htail hbound i ht,
    roundedVertexPath_eq_local _ hδ hδhalf htail hbound i ht]
  rw [polygonDeleteVertex_last_integer p (by omega) (by omega),
    polygonDeleteVertex_last_integer p (by omega) (by omega),
    polygonDeleteVertex_last_integer p (by omega) (by omega)]


theorem roundedPolygon_delete_last_eq_at_zero (p : Polygon E (n + 4))
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ} (ht : |t| < 3 / 4) :
    roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3)))
        (deletionClock ρ (n + 4) t) =
      roundedCorner ρ (p 0) ((2 : ℝ) • (p 0 - p (Fin.last (n + 3))))
        (p ⟨1, by omega⟩ - p 0) (deletionClock ρ (n + 4) t) := by
  have hhalf : δ < 1 / 2 := by linarith
  have ht' : t ∈ Ioo (-1 + δ) (1 - δ) := by
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hc := deletionClock_eq_at_zero (N := n + 4) (by omega) hδ hhalf htail hbound ht'
  have hct : deletionClock ρ (n + 4) t ∈ Ioo (-1 + δ) (1 - δ) := by
    rw [hc]
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2, (hbound t).1,
      (hbound t).2, abs_nonneg t]
  have hct' : deletionClock ρ (n + 4) t ∈ Ioo ((0 : ℤ) - 1 + δ)
      ((0 : ℤ) + 1 - δ) := by simpa using hct
  change roundedVertexPath ρ _ _ = _
  rw [roundedVertexPath_eq_local _ hδ hhalf htail hbound 0 hct']
  simp only [zero_sub, zero_add, polygonIntegerIndex_zero, polygonIntegerIndex_neg_one,
    polygonIntegerIndex_one (show 1 < n + 3 by omega), polygonDeleteVertex_last_apply,
    Int.cast_zero, sub_zero]
  have heq : p (0 : Fin (n + 3)).castSucc - p (Fin.last (n + 2)).castSucc =
      (2 : ℝ) • (p 0 - p (Fin.last (n + 3))) := by
    rw [hmid, midpoint_eq_smul_add, invOf_eq_inv]
    change p 0 - p (Fin.last (n + 2)).castSucc = _
    module
  rw [heq]
  rfl

theorem roundedPolygonParameter_eq_at_last (p : Polygon E (n + 2))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : t ∈ Ioo ((n : ℝ) + δ) ((n : ℝ) + 2 - δ)) :
    roundedPolygonParameter ρ p t = roundedCorner ρ (p (Fin.last (n + 1)))
      (p (Fin.last (n + 1)) - p (Fin.last n).castSucc)
      (p 0 - p (Fin.last (n + 1))) (t - ((n : ℝ) + 1)) := by
  have ht' : t ∈ Ioo (((n + 1 : ℕ) : ℤ) - 1 + δ) (((n + 1 : ℕ) : ℤ) + 1 - δ) := by
    push_cast
    constructor <;> linarith [ht.1, ht.2]
  change roundedVertexPath ρ _ _ = _
  rw [roundedVertexPath_eq_local _ hδ hδhalf htail hbound (n + 1 : ℕ) ht']
  have hidx : polygonIntegerIndex (n + 2) ((n + 1 : ℕ) : ℤ) = Fin.last (n + 1) :=
    polygonIntegerIndex_nat (Fin.last (n + 1))
  have hidxprev : polygonIntegerIndex (n + 2) (((n + 1 : ℕ) : ℤ) - 1) =
      (Fin.last n).castSucc := by
    rw [show (((n + 1 : ℕ) : ℤ) - 1) = n by omega]
    exact polygonIntegerIndex_nat (Fin.last n).castSucc
  have hidxnext : polygonIntegerIndex (n + 2) (((n + 1 : ℕ) : ℤ) + 1) = 0 := by
    rw [show (((n + 1 : ℕ) : ℤ) + 1) = (n + 2 : ℕ) by omega]
    exact polygonIntegerIndex_self
  simp only [Nat.cast_add, Nat.cast_one] at hidx hidxprev hidxnext ⊢
  simp only [hidx, hidxprev, hidxnext, Int.cast_add, Int.cast_natCast, Int.cast_one]


theorem roundedPolygon_delete_last_eq_at_penultimate_parameter (p : Polygon E (n + 4))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : t ∈ Ioo ((n : ℝ) + 1 + δ) ((n : ℝ) + 3 - δ)) :
    roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3))) t =
      roundedCorner ρ (p (Fin.last (n + 2)).castSucc)
        (p (Fin.last (n + 2)).castSucc - p (Fin.last (n + 1)).castSucc.castSucc)
        (p 0 - p (Fin.last (n + 2)).castSucc) (t - ((n : ℝ) + 2)) := by
  have ht' : t ∈ Ioo (((n + 1 : ℕ) : ℝ) + δ) (((n + 1 : ℕ) : ℝ) + 2 - δ) := by
    push_cast
    constructor <;> linarith [ht.1, ht.2]
  rw [roundedPolygonParameter_eq_at_last _ hδ hδhalf htail hbound ht']
  simp only [polygonDeleteVertex_last_apply, Nat.cast_add, Nat.cast_one, Fin.castSucc_zero]
  congr 2
  ring


theorem roundedPolygon_delete_last_eq_at_last (p : Polygon E (n + 4))
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : |t - ((n : ℝ) + 3)| < 3 / 4) :
    roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3)))
        (deletionClock ρ (n + 4) t) = roundedPolygonParameter ρ p t := by
  have hhalf : δ < 1 / 2 := by linarith
  have ht' : t ∈ Ioo (((n + 4 : ℕ) : ℝ) - 2 + δ) (((n + 4 : ℕ) : ℝ) - δ) := by
    push_cast
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hc : deletionClock ρ (n + 4) t = (t + (n : ℝ) + 2) / 2 := by
    rw [deletionClock_eq_at_last (by omega) hδ hhalf htail hbound ht']
    push_cast
    ring
  have hct : deletionClock ρ (n + 4) t ∈ Ioo ((n : ℝ) + 1 + δ) ((n : ℝ) + 3 - δ) := by
    rw [hc]
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hcttail : δ ≤ deletionClock ρ (n + 4) t - ((n : ℝ) + 2) := by
    rw [hc]
    linarith [(abs_lt.mp ht).1]
  have htlast : t ∈ Ioo (((n + 2 : ℕ) : ℝ) + δ) (((n + 2 : ℕ) : ℝ) + 2 - δ) := by
    push_cast
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  rw [roundedPolygon_delete_last_eq_at_penultimate_parameter p hδ hhalf htail hbound hct,
    (roundedCorner_tail_bounds _ _ _ hδ htail hbound).2.1 _ hcttail,
    roundedPolygonParameter_eq_at_last p hδ hhalf htail hbound htlast,
    hc, hmid, midpoint_eq_smul_add, invOf_eq_inv]
  simp only [roundedCorner, Nat.cast_add, Nat.cast_ofNat]
  module


theorem roundedPolygon_delete_last_eq_at_penultimate (p : Polygon E (n + 4))
    (hmid : p (Fin.last (n + 3)) =
      midpoint ℝ (p (Fin.last (n + 2)).castSucc) (p 0))
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 8)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) {t : ℝ}
    (ht : |t - ((n : ℝ) + 2)| < 3 / 4) :
    roundedPolygonParameter ρ (polygonDeleteVertex p (Fin.last (n + 3)))
        (deletionClock ρ (n + 4) t) =
      roundedCorner ρ (p (Fin.last (n + 2)).castSucc)
        (p (Fin.last (n + 2)).castSucc - p (Fin.last (n + 1)).castSucc.castSucc)
        ((2 : ℝ) • (p (Fin.last (n + 3)) - p (Fin.last (n + 2)).castSucc))
        (deletionClock ρ (n + 4) t - ((n : ℝ) + 2)) := by
  have hhalf : δ < 1 / 2 := by linarith
  have ht' : t ∈ Ioo (((n + 4 : ℕ) : ℝ) - 3 + δ)
      (((n + 4 : ℕ) : ℝ) - 1 - δ) := by
    push_cast
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hc : deletionClock ρ (n + 4) t = (n : ℝ) + 2 +
      (3 * (t - ((n : ℝ) + 2)) - ρ (t - ((n : ℝ) + 2))) / 4 := by
    have heq : ((n + 4 : ℕ) : ℝ) - 2 = (n : ℝ) + 2 := by push_cast; ring
    simpa only [heq] using deletionClock_eq_at_penultimate (N := n + 4) (by omega)
      hδ hhalf htail hbound ht'
  have hct : deletionClock ρ (n + 4) t ∈ Ioo ((n : ℝ) + 1 + δ) ((n : ℝ) + 3 - δ) := by
    rw [hc]
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2,
      (hbound (t - ((n : ℝ) + 2))).1, (hbound (t - ((n : ℝ) + 2))).2,
      abs_nonneg (t - ((n : ℝ) + 2))]
  rw [roundedPolygon_delete_last_eq_at_penultimate_parameter p hδ hhalf htail hbound hct]
  have heq : p 0 - p (Fin.last (n + 2)).castSucc =
      (2 : ℝ) • (p (Fin.last (n + 3)) - p (Fin.last (n + 2)).castSucc) := by
    rw [hmid, midpoint_eq_smul_add, invOf_eq_inv]
    module
  rw [heq]

end Poincare.Manifold.Schoenflies.Plane
