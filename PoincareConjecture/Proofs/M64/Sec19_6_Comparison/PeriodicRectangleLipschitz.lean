import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing











set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal NNReal

namespace PoincareConjecture

private theorem annulusPoint_coordinates (p : LoopPlane) :
    annulusPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl




theorem m64_periodic_rectangle_lipschitz_translate
    {Y : Type*} [PseudoEMetricSpace Y] {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {K : ℝ≥0} (hLip : LipschitzOnWith K f m64AnnulusDomain) (k : ℤ) :
    LipschitzOnWith K f {p | (k : ℝ) * curvePeriod ≤ p 0 ∧
      p 0 ≤ (k : ℝ) * curvePeriod + curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1} := by
  let v := annulusPoint ((k : ℝ) * curvePeriod) 0
  have heq (p : LoopPlane) : f (p - v) = f p := by
    have hp : Function.Periodic (fun x => f (annulusPoint x (p 1))) curvePeriod :=
      fun x => hperiodic x (p 1)
    have h := hp.int_mul k (p 0 - (k : ℝ) * curvePeriod)
    have hpoint : p - v = annulusPoint (p 0 - (k : ℝ) * curvePeriod) (p 1) := by
      ext i
      fin_cases i <;> simp [v, annulusPoint]
    rw [hpoint]
    simpa only [sub_add_cancel, annulusPoint_coordinates] using h.symm
  have hmem {p : LoopPlane}
      (hp : (k : ℝ) * curvePeriod ≤ p 0 ∧
        p 0 ≤ (k : ℝ) * curvePeriod + curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) :
      p - v ∈ m64AnnulusDomain := by
    change 0 ≤ (p - v) 0 ∧ (p - v) 0 ≤ curvePeriod ∧
      0 ≤ (p - v) 1 ∧ (p - v) 1 ≤ 1
    simp only [PiLp.sub_apply, v, annulusPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
    exact ⟨by linarith [hp.1], by linarith [hp.2.1], hp.2.2⟩
  intro p hp q hq
  have h := hLip (hmem hp) (hmem hq)
  simpa only [heq, edist_sub_right] using h




theorem m64_periodic_rectangle_locally_lipschitz
    {Y : Type*} [PseudoEMetricSpace Y] {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {K : ℝ≥0} (hLip : LipschitzOnWith K f m64AnnulusDomain) :
    LocallyLipschitzOn {p : LoopPlane | 0 ≤ p 1 ∧ p 1 ≤ 1} f := by
  classical
  intro p hp
  let k : ℤ := Int.floor (p 0 / curvePeriod)
  let lo : ℝ := ((k : ℝ) - 1) * curvePeriod
  let mid : ℝ := (k : ℝ) * curvePeriod
  let hi : ℝ := ((k : ℝ) + 1) * curvePeriod
  let S : Set LoopPlane := {q | lo ≤ q 0 ∧ q 0 ≤ hi ∧ 0 ≤ q 1 ∧ q 1 ≤ 1}
  have hlo : lo < p 0 := by
    have h := (le_div_iff₀ Real.two_pi_pos).mp (Int.floor_le (p 0 / curvePeriod))
    dsimp only [lo, k, curvePeriod] at h ⊢
    nlinarith [Real.pi_pos]
  have hhi : p 0 < hi := by
    have h := (div_lt_iff₀ Real.two_pi_pos).mp (Int.lt_floor_add_one (p 0 / curvePeriod))
    simpa only [hi, k, curvePeriod] using h
  have hconvex : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    change lo ≤ (a • x + b • y) 0 ∧ (a • x + b • y) 0 ≤ hi ∧
      0 ≤ (a • x + b • y) 1 ∧ (a • x + b • y) 1 ≤ 1
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, add_nonneg (mul_nonneg ha hx.2.2.1)
      (mul_nonneg hb hy.2.2.1), ?_⟩
    · calc
        lo = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
        _ ≤ a * x 0 + b * y 0 := add_le_add
          (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
    · calc
        a * x 0 + b * y 0 ≤ a * hi + b * hi := add_le_add
          (mul_le_mul_of_nonneg_left hx.2.1 ha) (mul_le_mul_of_nonneg_left hy.2.1 hb)
        _ = hi := by rw [← add_mul, hab, one_mul]
    · calc
        a * x 1 + b * y 1 ≤ a * 1 + b * 1 := add_le_add
          (mul_le_mul_of_nonneg_left hx.2.2.2 ha)
          (mul_le_mul_of_nonneg_left hy.2.2.2 hb)
        _ = 1 := by rw [← add_mul, hab, one_mul]
  have hleft : LipschitzOnWith K f (S ∩ {q | q 0 ≤ mid}) := by
    apply (m64_periodic_rectangle_lipschitz_translate hperiodic hLip (k - 1)).mono
    intro q hq
    refine ⟨?_, ?_, hq.1.2.2⟩
    · simpa only [Int.cast_sub, Int.cast_one] using hq.1.1
    · simp only [Int.cast_sub, Int.cast_one]
      calc
        q 0 ≤ (k : ℝ) * curvePeriod := hq.2
        _ = ((k : ℝ) - 1) * curvePeriod + curvePeriod := by ring
  have hright : LipschitzOnWith K f (S ∩ {q | mid ≤ q 0}) := by
    apply (m64_periodic_rectangle_lipschitz_translate hperiodic hLip k).mono
    intro q hq
    refine ⟨hq.2, ?_, hq.1.2.2⟩
    calc
      q 0 ≤ hi := hq.1.2.1
      _ = (k : ℝ) * curvePeriod + curvePeriod := by dsimp only [hi]; ring
  have hglue := M60.lipschitzOnWith_piecewise_of_convex hconvex
    (fun q : LoopPlane => q 0)
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousOn mid hleft hright
    (fun _ _ _ => rfl)
  have hS : S ∈ 𝓝[{q : LoopPlane | 0 ≤ q 1 ∧ q 1 ≤ 1}] p := by
    have hopen : IsOpen {q : LoopPlane | lo < q 0 ∧ q 0 < hi} :=
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
        (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0) continuous_const)
    apply mem_of_superset (inter_mem (nhdsWithin_le_nhds (hopen.mem_nhds ⟨hlo, hhi⟩))
      self_mem_nhdsWithin)
    intro q hq
    exact ⟨hq.1.1.le, hq.1.2.le, hq.2⟩
  refine ⟨K, S, hS, ?_⟩
  simpa only [piecewise_same, max_self] using hglue

end PoincareConjecture
