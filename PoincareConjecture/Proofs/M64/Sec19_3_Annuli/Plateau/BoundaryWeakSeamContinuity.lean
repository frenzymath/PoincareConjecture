import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakSeamOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseContinuity

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

theorem m64WeakPhase_monotone_trace_equicontinuousAt_seam
    {I : Type*} (u : I → LoopPlane → ℝ) (V : I → Fin 2 → LoopPlane → ℝ)
    (b : I → ℝ → ℝ) (D : I → ℝ)
    (hV : ∀ j i, MemLp (V j i) 2 mu) (hb : ∀ j, Monotone (b j))
    (hbperiod : ∀ j x, b j (x + curvePeriod) = b j x + D j)
    (hseam : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V j 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u j p) =
        D j * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen1 : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V j 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u j p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b j x))
    {E : ℝ} (hE : ∀ j, (∫ p in S, (V j 0 p) ^ 2) + ∫ p in S, (V j 1 p) ^ 2 ≤ E) :
    EquicontinuousAt b 0 := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let R : ℝ := min (curvePeriod / 4) (1 / 2)
  have hR : 0 < R := lt_min (by positivity) (by norm_num)
  have hRP : 2 * R < curvePeriod := by
    have hh : R ≤ curvePeriod / 4 := min_le_left _ _
    linarith
  have hR1 : R < 1 := (min_le_right _ _).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  let C : ℝ := 8 * ((∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e0) ^ 2) +
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
  have hgap := m64WeakPhase_monotone_seam_gap_sq_le (u j) (V j) (b j) (D j)
    (hV j) (hb j) (hbperiod j) (hseam j) (hgreen1 j) hR hRP hR1 hNpos
  have hgap' : (b j d - b j (-d)) ^ 2 < eps ^ 2 := by
    have hbound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hE j) hC) (Nat.cast_nonneg N)
    exact (hgap.trans hbound).trans_lt hsmallN
  have hspan : b j d - b j (-d) < eps := by nlinarith
  have hy' := abs_lt.mp (show |y| < d by simpa only [Real.dist_eq, sub_zero] using hy)
  have hlx := hb j (show -d ≤ 0 by linarith)
  have hxu := hb j (show 0 ≤ d by linarith)
  have hly := hb j (show -d ≤ y by linarith)
  have hyu := hb j (show y ≤ d by linarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem m64Continuous_of_affine_period_of_continuousAt_zero
    (b : ℝ → ℝ) {T D : ℝ} (hT : 0 < T)
    (hp : ∀ x, b (x + T) = b x + D)
    (h0 : ContinuousAt b 0) (hI : ContinuousOn b (Ioo (0 : ℝ) T)) : Continuous b := by
  let f : ℝ → ℝ := fun x => b x - D / T * x
  have hf : Function.Periodic f T := by
    intro x
    dsimp only [f]
    rw [hp]
    field_simp
    ring
  have hf0 : ContinuousAt f 0 := h0.sub (continuousAt_const.mul continuousAt_id)
  have hfI : ContinuousOn f (Ioo (0 : ℝ) T) :=
    hI.sub (continuous_const.mul continuous_id).continuousOn
  have hfc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    let k : ℤ := ⌊x / T⌋
    let y := x - (k : ℝ) * T
    have hy0 : 0 ≤ y := by
      have hh := (le_div_iff₀ hT).mp (Int.floor_le (x / T))
      dsimp only [y, k]
      linarith
    have hyT : y < T := by
      have hh := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (x / T))
      dsimp only [y, k]
      linarith
    have hfy : ContinuousAt f y := by
      rcases eq_or_lt_of_le hy0 with heq | hpos
      · simpa only [← heq] using hf0
      · exact (hfI y ⟨hpos, hyT⟩).continuousAt (Ioo_mem_nhds hpos hyT)
    have hshift : ContinuousAt (fun z : ℝ => f (z - (k : ℝ) * T)) x :=
      hfy.comp_of_eq (show ContinuousAt (fun z : ℝ => z - (k : ℝ) * T) x from
        continuousAt_id.sub continuousAt_const) rfl
    have heq : (fun z : ℝ => f (z - (k : ℝ) * T)) = f :=
      funext (hf.int_mul k).sub_eq
    rwa [heq] at hshift
  have heq : b = fun x => f x + D / T * x := by ext x; dsimp only [f]; ring
  rw [heq]
  exact hfc.add (continuous_const.mul continuous_id)

theorem m64WeakPhase_monotone_affine_trace_continuous
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ) (D : ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu) (hb : Monotone b)
    (hbperiod : ∀ x, b (x + curvePeriod) = b x + D)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x)) :
    Continuous b := by
  have heq := m64WeakPhase_monotone_trace_equicontinuousAt_seam
    (I := Unit) (fun _ => u) (fun _ => V) (fun _ => b) (fun _ => D)
    (fun _ => hV) (fun _ => hb) (fun _ => hbperiod)
    (fun _ => hseam) (fun _ => hgreen1) (fun _ => le_rfl)
  apply m64Continuous_of_affine_period_of_continuousAt_zero b
    (by unfold curvePeriod; positivity) hbperiod (heq.continuousAt ())
  apply m64WeakPhase_monotone_trace_continuousOn u V b hV hb _ hgreen1
  intro phi hphi hleft hright
  have h := hseam phi hphi (fun s _ => by rw [hright, hleft])
  simpa only [hright, integral_zero, mul_zero] using h

end PoincareConjecture
