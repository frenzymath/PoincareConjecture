import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedCorner
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic

set_option autoImplicit false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def roundedVertexPath (ρ : ℝ → ℝ) (P : ℤ → E) (t : ℝ) : E :=
  let j := ⌊t + 1 / 2⌋
  roundedCorner ρ (P j) (P j - P (j - 1)) (P (j + 1) - P j) (t - j)

theorem roundedVertexPath_eq_local {ρ : ℝ → ℝ} (P : ℤ → E) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (i : ℤ) {t : ℝ} (ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ)) :
    roundedVertexPath ρ P t =
      roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i) (t - i) := by
  let j : ℤ := ⌊t + 1 / 2⌋
  have hjlo : (j : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hjhi : t + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hji : i - 2 < j := by
    have h : (i : ℝ) - 2 < j := by linarith [ht.1]
    exact_mod_cast h
  have hij : j < i + 2 := by
    have h : (j : ℝ) < (i : ℝ) + 2 := by linarith [ht.2]
    exact_mod_cast h
  have hcases : j = i - 1 ∨ j = i ∨ j = i + 1 := by omega
  change roundedCorner ρ (P j) (P j - P (j - 1)) (P (j + 1) - P j) (t - j) = _
  rcases hcases with hj | hj | hj
  · rw [hj] at hjhi ⊢
    rw [Int.cast_sub, Int.cast_one] at hjhi ⊢
    have hleft : t - (i : ℝ) ≤ -δ := by linarith
    have hright : δ ≤ t - ((i : ℝ) - 1) := by linarith [ht.1]
    rw [(roundedCorner_tail_bounds _ _ _ hδ htail hbound).2.1 _ hright,
      (roundedCorner_tail_bounds _ _ _ hδ htail hbound).1 _ hleft]
    simp only [sub_add_cancel]
    module
  · rw [hj]
  · rw [hj] at hjlo ⊢
    rw [Int.cast_add, Int.cast_one] at hjlo ⊢
    have hleft : t - ((i : ℝ) + 1) ≤ -δ := by linarith [ht.2]
    have hright : δ ≤ t - (i : ℝ) := by linarith
    rw [(roundedCorner_tail_bounds _ _ _ hδ htail hbound).1 _ hleft,
      (roundedCorner_tail_bounds _ _ _ hδ htail hbound).2.1 _ hright]
    simp only [add_sub_cancel_right]
    module

theorem contDiff_roundedVertexPath {ρ : ℝ → ℝ} {P : V → ℤ → E} {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hP : ∀ i, ContDiff ℝ ∞ (fun z => P z i)) :
    ContDiff ℝ ∞ (fun x : V × ℝ => roundedVertexPath ρ (P x.1) x.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let i : ℤ := ⌊x.2 + 1 / 2⌋
  have hilo : (i : ℝ) ≤ x.2 + 1 / 2 := Int.floor_le _
  have hihi : x.2 + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have hx : x.2 ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
    constructor <;> linarith
  have hF : ContDiff ℝ ∞ (fun y : V × ℝ =>
      roundedCorner ρ (P y.1 i) (P y.1 i - P y.1 (i - 1))
        (P y.1 (i + 1) - P y.1 i) (y.2 - i)) :=
    (contDiff_roundedCorner hρ (hP i) ((hP i).sub (hP (i - 1)))
      ((hP (i + 1)).sub (hP i))).comp
      (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  apply hF.contDiffAt.congr_of_eventuallyEq
  have hU : ∀ᶠ y : V × ℝ in 𝓝 x,
      y.2 ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) :=
    continuous_snd.continuousAt (isOpen_Ioo.mem_nhds hx)
  filter_upwards [hU] with y hy
  exact roundedVertexPath_eq_local (P y.1) hδ hδhalf htail hbound i hy

theorem periodic_roundedVertexPath (ρ : ℝ → ℝ) (P : ℤ → E) (n : ℤ)
    (hP : ∀ i, P (i + n) = P i) : Periodic (roundedVertexPath ρ P) (n : ℝ) := by
  intro t
  have hfloor : ⌊t + (n : ℝ) + 1 / 2⌋ = ⌊t + 1 / 2⌋ + n := by
    rw [show t + (n : ℝ) + 1 / 2 = (t + 1 / 2) + n by ring,
      Int.floor_add_intCast]
  simp only [roundedVertexPath, hfloor, Int.cast_add]
  rw [show ⌊t + 1 / 2⌋ + n - 1 = (⌊t + 1 / 2⌋ - 1) + n by omega,
    show ⌊t + 1 / 2⌋ + n + 1 = (⌊t + 1 / 2⌋ + 1) + n by omega]
  simp only [hP]
  congr 1
  ring

end Poincare.Manifold.Schoenflies.Plane
