import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCircleArc
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Topology

namespace PoincareConjecture

private theorem m65PuncturedArg_uniform (p : LoopCircle) {ρ η : ℝ}
    (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ δ > 0, ∀ x y : LoopCircle, ρ ≤ dist x p → ρ ≤ dist y p → dist x y < δ →
      |m65WeakCircleArg p x - m65WeakCircleArg p y| < η := by
  let K : Set LoopCircle := {x | ρ ≤ dist x p}
  have hK : IsCompact K :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hf : ContinuousOn (m65WeakCircleArg p) K := by
    intro x hx
    have hxp : x ≠ p := by
      intro he
      have := hx
      simp only [K, mem_ofPred_eq, he, dist_self] at this
      exact (not_le_of_gt hρ) this
    exact ((m65WeakCircleArg_continuousAt hxp).comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, fun x y hx hy hxy => ?_⟩
  simpa only [Real.dist_eq] using hd x hx y hy hxy

private theorem m65ThreePins_separated (q : Fin 3 → LoopCircle)
    (hq : Function.Injective q) :
    ∃ ρ > 0, ∀ i j : Fin 3, i ≠ j → 4 * ρ ≤ dist (q i) (q j) := by
  let d := min (dist (q 0) (q 1)) (min (dist (q 0) (q 2)) (dist (q 1) (q 2)))
  have hdpos : 0 < d := lt_min
    (dist_pos.mpr (hq.ne (by decide)))
    (lt_min (dist_pos.mpr (hq.ne (by decide))) (dist_pos.mpr (hq.ne (by decide))))
  have h01 : d ≤ dist (q 0) (q 1) := min_le_left _ _
  have h02 : d ≤ dist (q 0) (q 2) := (min_le_right _ _).trans (min_le_left _ _)
  have h12 : d ≤ dist (q 1) (q 2) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d / 4, by positivity, ?_⟩
  intro i j hij
  have he : 4 * (d / 4) = d := by ring
  rw [he]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · exact h01.trans_eq (dist_comm _ _)
  · exact (hij rfl).elim
  · exact h12
  · exact h02.trans_eq (dist_comm _ _)
  · exact h12.trans_eq (dist_comm _ _)
  · exact (hij rfl).elim

private theorem m65Arc_two_exterior_pins (p : Fin 3 → LoopCircle)
    (hp : ∀ i j : Fin 3, i ≠ j → 1 ≤ dist (p i) (p j))
    (s : ℝ → LoopCircle) {a b : ℝ}
    (hdiam : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist (s x) (s y) < 1) :
    ∃ i j : Fin 3, i ≠ j ∧ (∀ t ∈ Icc a b, s t ≠ p i) ∧
      (∀ t ∈ Icc a b, s t ≠ p j) := by
  let O (i : Fin 3) := ∀ t ∈ Icc a b, s t ≠ p i
  have hex {i j : Fin 3} (hij : i ≠ j) (hi : ¬O i) : O j := by
    dsimp only [O] at hi ⊢
    push Not at hi
    obtain ⟨x, hx, he⟩ := hi
    intro y hy hey
    have hd := hdiam x hx y hy
    rw [he, hey] at hd
    exact (not_lt_of_ge (hp i j hij)) hd
  by_cases h0 : O 0
  · by_cases h1 : O 1
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, hex (by decide : (1 : Fin 3) ≠ 2) h1⟩
  · exact ⟨1, 2, by decide, hex (by decide : (0 : Fin 3) ≠ 1) h0,
      hex (by decide : (0 : Fin 3) ≠ 2) h0⟩

theorem m65ThreePin_weak_arc_modulus (q : Fin 3 → LoopCircle)
    (hq : Function.Injective q) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ (β : C(LoopCircle, LoopCircle)), M65WeakCircleParameter β →
      ∀ (p : Fin 3 → LoopCircle),
      (∀ i j : Fin 3, i ≠ j → 1 ≤ dist (p i) (p j)) →
      (∀ i, β (p i) = q i) →
      ∀ (s : ℝ → LoopCircle) (a b : ℝ), a ≤ b →
      ContinuousOn s (Icc a b) → InjOn s (Icc a b) →
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist (s x) (s y) < 1) →
      dist (β (s a)) (β (s b)) < δ →
      ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, dist (β (s t)) (β (s u)) < η := by
  obtain ⟨ρ, hρ, hsep⟩ := m65ThreePins_separated q hq
  choose d hdpos hd using fun i => m65PuncturedArg_uniform (q i) hρ hη
  let δ := min ρ (min (d 0) (min (d 1) (d 2)))
  have hδpos : 0 < δ := lt_min hρ (lt_min (hdpos 0) (lt_min (hdpos 1) (hdpos 2)))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδd (i : Fin 3) : δ ≤ d i := by
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδpos, ?_⟩
  intro β hβ p hp hmap s a b hab hs hsi hdiam hend t ht u hu
  obtain ⟨i, j, hij, hi, hj⟩ := m65Arc_two_exterior_pins p hp s hdiam
  have hfar : 2 * ρ ≤ dist (β (s a)) (q i) ∨ 2 * ρ ≤ dist (β (s a)) (q j) := by
    by_contra! h
    have htri := dist_triangle (q i) (β (s a)) (q j)
    rw [dist_comm (q i) (β (s a))] at htri
    have hsepij := hsep i j hij
    linarith
  obtain ⟨k, hk, hka⟩ : ∃ k : Fin 3,
      (∀ x ∈ Icc a b, s x ≠ p k) ∧ 2 * ρ ≤ dist (β (s a)) (q k) := by
    rcases hfar with h | h
    · exact ⟨i, hi, h⟩
    · exact ⟨j, hj, h⟩
  have hkb : ρ ≤ dist (β (s b)) (q k) := by
    have htri := dist_triangle (β (s a)) (β (s b)) (q k)
    have hh := hend.trans_le hδρ
    linarith
  have hka' : ρ ≤ dist (β (s a)) (q k) := by linarith
  have hane : β (s a) ≠ β (p k) := by
    rw [hmap k]
    exact dist_pos.mp (hρ.trans_le hka')
  have hbne : β (s b) ≠ β (p k) := by
    rw [hmap k]
    exact dist_pos.mp (hρ.trans_le hkb)
  calc
    _ ≤ |m65WeakCircleArg (β (p k)) (β (s a)) -
        m65WeakCircleArg (β (p k)) (β (s b))| :=
      m65WeakCircleParameter_arc_dist β hβ s hab hs hsi (p k) hk hane hbne ht hu
    _ < η := by
      rw [hmap k]
      exact hd k (β (s a)) (β (s b)) hka' hkb (hend.trans_le (hδd k))

end PoincareConjecture
