import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ

theorem scalar_periodic_strip_locallyLipschitz
    {Y : Type*} [PseudoEMetricSpace Y] (f : Cover → Y) {L : ℝ≥0}
    (hL : LipschitzOnWith L f {z | z.1 ∈ Icc (0 : ℝ) 1})
    (hperiod : ∀ x s : ℝ, f (x + 1, s) = f (x, s)) : LocallyLipschitz f := by
  classical
  let S : Set Cover := {z | z.1 ∈ Icc (-1 : ℝ) 1}
  have hshift : LipschitzWith 1 (fun z : Cover => z + (1, 0)) :=
    LipschitzWith.of_dist_le_mul (fun _ _ => by simp [dist_eq_norm])
  have hleft : LipschitzOnWith L f (S ∩ {z | z.1 ≤ 0}) := by
    have hmaps : MapsTo (fun z : Cover => z + (1, 0))
        (S ∩ {z | z.1 ≤ 0}) {z | z.1 ∈ Icc (0 : ℝ) 1} := by
      intro z hz
      change 0 ≤ z.1 + 1 ∧ z.1 + 1 ≤ 1
      have hz' : -1 ≤ z.1 ∧ z.1 ≤ 1 := hz.1
      have hz0 : z.1 ≤ 0 := hz.2
      constructor <;> linarith
    have h := hL.comp hshift.lipschitzOnWith hmaps
    have heq (z : Cover) : f (z + (1, 0)) = f z := by
      change f (z.1 + 1, z.2 + 0) = f z
      simpa only [add_zero, Prod.eta] using hperiod z.1 z.2
    intro z hz w hw
    simpa only [Function.comp_apply, heq, mul_one] using h hz hw
  have hright : LipschitzOnWith L f (S ∩ {z | 0 ≤ z.1}) :=
    hL.mono (fun _ hz => ⟨hz.2, hz.1.2⟩)
  have hSconvex : Convex ℝ S :=
    (convex_Icc (-1 : ℝ) 1).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have hS : LipschitzOnWith L f S := by
    simpa only [piecewise_same, max_self] using
      M60.lipschitzOnWith_piecewise_of_convex hSconvex Prod.fst continuous_fst.continuousOn
        0 hleft hright (fun _ _ _ => rfl)
  have hperiod_int (z : Cover) (k : ℤ) : f (z - ((k : ℝ), 0)) = f z := by
    have h : Function.Periodic (fun t : ℝ => f (t, z.2)) 1 := fun t => hperiod t z.2
    change f (z.1 - (k : ℝ), z.2 - 0) = f z
    simpa only [sub_zero, mul_one, Prod.eta] using
      h.sub_int_mul_eq (x := z.1) k
  intro x
  let k : ℤ := ⌊x.1⌋
  let T : Cover → Cover := fun z => z - ((k : ℝ), 0)
  let V : Set Cover := {z | z.1 - (k : ℝ) ∈ Ioo (-1 : ℝ) 1}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_fst.sub continuous_const)
  have hxV : x ∈ V := by
    have hlo := Int.fract_nonneg x.1
    have hhi := Int.fract_lt_one x.1
    change -1 < x.1 - (k : ℝ) ∧ x.1 - (k : ℝ) < 1
    dsimp only [Int.fract] at hlo hhi
    exact ⟨by dsimp only [k]; linarith, hhi⟩
  have hT : LipschitzWith 1 T :=
    LipschitzWith.of_dist_le_mul (fun _ _ => by simp [T, dist_eq_norm])
  have hmaps : MapsTo T V S := fun _ hz => ⟨hz.1.le, hz.2.le⟩
  have h := hS.comp hT.lipschitzOnWith hmaps
  refine ⟨L, V, hV.mem_nhds hxV, ?_⟩
  intro z hz w hw
  simpa only [Function.comp_apply, T, hperiod_int, mul_one] using h hz hw

end PoincareConjecture.M64Uniformization
