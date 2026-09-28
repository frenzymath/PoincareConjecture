import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic









set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_nonnested_reference_quartic_chart :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      e.source = {p : ℝ × ℝ | 0 < p.1} ∧
      e.target = {p : ℝ × ℝ | 0 < p.1} ∧
      (∀ p : ℝ × ℝ, e p = (p.1, p.2 * Real.sqrt (p.1 + p.2 ^ 2))) ∧
      (∀ p : ℝ × ℝ, e.symm p =
        (p.1, Real.sqrt 2 * p.2 /
          Real.sqrt (p.1 + Real.sqrt (p.1 ^ 2 + 4 * p.2 ^ 2)))) ∧
      ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.source, (e p).2 ^ 2 = p.2 ^ 2 * (p.1 + p.2 ^ 2)) ∧
      ∀ p ∈ e.target, (e.symm p).2 ^ 2 =
        (Real.sqrt (p.1 ^ 2 + 4 * p.2 ^ 2) - p.1) / 2 := by
  classical
  let U : Set (ℝ × ℝ) := {p | 0 < p.1}
  let f : ℝ → ℝ → ℝ := fun b t => t * Real.sqrt (b + t ^ 2)
  let k : ℝ → ℝ → ℝ := fun b Y =>
    Real.sqrt 2 * Y / Real.sqrt (b + Real.sqrt (b ^ 2 + 4 * Y ^ 2))
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, f p.1 p.2)
  let G : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, k p.1 p.2)
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwoSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hF : ContDiffOn ℝ ∞ F U := by
    refine contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.mul ?_)
    exact (contDiff_fst.add (contDiff_snd.pow 2)).contDiffOn.sqrt (fun p hp => by
      have hp' : 0 < p.1 := hp
      positivity)
  have hinner : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + 4 * p.2 ^ 2)) U := by
    exact ((contDiff_fst.pow 2).add
      (contDiff_const.mul (contDiff_snd.pow 2))).contDiffOn.sqrt (fun p hp => by
        have hp' : 0 < p.1 := hp
        positivity)
  have houter : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => Real.sqrt (p.1 + Real.sqrt (p.1 ^ 2 + 4 * p.2 ^ 2)))
      U := by
    exact (contDiff_fst.contDiffOn.add hinner).sqrt (fun p hp => by
      have hp' : 0 < p.1 := hp
      positivity)
  have hG : ContDiffOn ℝ ∞ G U := by
    refine contDiff_fst.contDiffOn.prodMk
      ((contDiffOn_const.mul contDiff_snd.contDiffOn).div houter ?_)
    intro p hp
    have hp' : 0 < p.1 := hp
    positivity
  have hfSq (b : ℝ) (hb : 0 < b) (t : ℝ) :
      (f b t) ^ 2 = t ^ 2 * (b + t ^ 2) := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hkf (b : ℝ) (hb : 0 < b) (t : ℝ) : k b (f b t) = t := by
    have hr : 0 < Real.sqrt (b + t ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hi : Real.sqrt (b ^ 2 + 4 * (f b t) ^ 2) = b + 2 * t ^ 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      rw [hfSq b hb t]
      ring
    have ho : Real.sqrt (b + (b + 2 * t ^ 2)) =
        Real.sqrt 2 * Real.sqrt (b + t ^ 2) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    dsimp [k]
    rw [hi, ho]
    dsimp [f]
    field_simp [hr.ne', htwo.ne']
  have hkSq (b : ℝ) (hb : 0 < b) (Y : ℝ) :
      (k b Y) ^ 2 = (Real.sqrt (b ^ 2 + 4 * Y ^ 2) - b) / 2 := by
    let S : ℝ := Real.sqrt (b ^ 2 + 4 * Y ^ 2)
    let B : ℝ := Real.sqrt (b + S)
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hS2 : S ^ 2 = b ^ 2 + 4 * Y ^ 2 := Real.sq_sqrt (by positivity)
    have hB2 : B ^ 2 = b + S := Real.sq_sqrt (by positivity)
    change (Real.sqrt 2 * Y / B) ^ 2 = (S - b) / 2
    rw [div_pow, mul_pow, htwoSq, hB2]
    apply (div_eq_iff (show b + S ≠ 0 by positivity)).2
    nlinarith only [hS2]
  have hfk (b : ℝ) (hb : 0 < b) (Y : ℝ) : f b (k b Y) = Y := by
    let S : ℝ := Real.sqrt (b ^ 2 + 4 * Y ^ 2)
    let B : ℝ := Real.sqrt (b + S)
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hB : 0 < B := Real.sqrt_pos.2 (by positivity)
    have hB2 : B ^ 2 = b + S := Real.sq_sqrt (by positivity)
    have ho : Real.sqrt (b + (k b Y) ^ 2) = B / Real.sqrt 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_pos hB htwo).le).2
      rw [hkSq b hb Y, div_pow, htwoSq, hB2]
      change b + (S - b) / 2 = (b + S) / 2
      ring
    dsimp [f]
    rw [ho]
    change (Real.sqrt 2 * Y / B) * (B / Real.sqrt 2) = Y
    field_simp [hB.ne', htwo.ne']
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    { toFun := F, invFun := G, source := U, target := U
      map_source' := fun _ hp => hp
      map_target' := fun _ hp => hp
      left_inv' := fun p hp => Prod.ext rfl (hkf p.1 hp p.2)
      right_inv' := fun p hp => Prod.ext rfl (hfk p.1 hp p.2)
      open_source := hU, open_target := hU
      continuousOn_toFun := hF.continuousOn
      continuousOn_invFun := hG.continuousOn }
  exact ⟨e, rfl, rfl, fun _ => rfl, fun _ => rfl, hF, hG,
    fun p hp => hfSq p.1 hp p.2, fun p hp => hkSq p.1 hp p.2⟩

end PoincareConjecture.M25.Topology3D
