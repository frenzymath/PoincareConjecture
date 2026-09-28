import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseOscillation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64WeakPhase_monotone_trace_equicontinuousAt
    {I : Type*} (u : I → LoopPlane → ℝ) (V : I → Fin 2 → LoopPlane → ℝ)
    (b : I → ℝ → ℝ) (hV : ∀ j i, MemLp (V j i) 2 mu) (hb : ∀ j, Monotone (b j))
    (hgreen0 : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V j 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u j p) = 0)
    (hgreen1 : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V j 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u j p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b j x))
    {E : ℝ} (hE : ∀ j, (∫ p in S, (V j 0 p) ^ 2) + ∫ p in S, (V j 1 p) ^ 2 ≤ E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) curvePeriod) : EquicontinuousAt b x := by
  let R : ℝ := min (min x (curvePeriod - x)) 1 / 2
  have hsmall : 0 < min (min x (curvePeriod - x)) 1 :=
    lt_min (lt_min hx.1 (sub_pos.mpr hx.2)) zero_lt_one
  have hR : 0 < R := half_pos hsmall
  have hRx : R < x := (half_lt_self hsmall).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hRP : x + R < curvePeriod := by
    have hh := (half_lt_self hsmall).trans_le
      ((min_le_left _ _).trans (min_le_right _ _))
    dsimp only [R]
    linarith
  have hR1 : R < 1 := (half_lt_self hsmall).trans_le (min_le_right _ _)
  let C : ℝ := 2 * ((∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e0) ^ 2) +
    ∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e1) ^ 2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num) (add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  apply Metric.equicontinuousAt_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C * E / eps ^ 2))
  have hNpos : 0 < N := by
    have hh : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN)
    exact_mod_cast hh
  have hsmallN : C * E / N < eps ^ 2 := by
    apply (div_lt_iff₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)).mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos heps)).mp ((le_max_right _ _).trans_lt hN)
    nlinarith
  let d := m64BoundaryCutoffRadius R N / 2
  have hd : 0 < d := half_pos (m64BoundaryCutoffRadius_pos hR N)
  refine ⟨d, hd, ?_⟩
  intro y hy j
  have hgap := m64WeakPhase_monotone_gap_sq_le (u j) (V j) (b j)
    (hV j) (hb j) (hgreen0 j) (hgreen1 j) hR hRx hRP hR1 hNpos
  have hgap' : (b j (x + d) - b j (x - d)) ^ 2 < eps ^ 2 := by
    have hbound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hE j) hC) (Nat.cast_nonneg N)
    exact (hgap.trans hbound).trans_lt hsmallN
  have hspan : b j (x + d) - b j (x - d) < eps := by nlinarith
  have hy' := abs_lt.mp (show |y - x| < d from hy)
  have hlx := hb j (show x - d ≤ x by linarith)
  have hxu := hb j (show x ≤ x + d by linarith)
  have hly := hb j (show x - d ≤ y by linarith)
  have hyu := hb j (show y ≤ x + d by linarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem m64WeakPhase_monotone_trace_continuousOn
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu) (hb : Monotone b)
    (hgreen0 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) = 0)
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x)) :
    ContinuousOn b (Ioo (0 : ℝ) curvePeriod) := by
  intro x hx
  have heq := m64WeakPhase_monotone_trace_equicontinuousAt
    (I := Unit) (fun _ => u) (fun _ => V) (fun _ => b) (fun _ => hV) (fun _ => hb)
    (fun _ => hgreen0) (fun _ => hgreen1) (fun _ => le_rfl) hx
  exact (heq.continuousAt ()).continuousWithinAt

end PoincareConjecture
