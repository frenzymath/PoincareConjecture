import PoincareConjecture.Proofs.M03.Existence.ChartStateSourceSmoothNative
import PoincareConjecture.Proofs.M03.Existence.CoordinateEllipticityNative
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option autoImplicit false
set_option maxHeartbeats 1800000

open Set MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

abbrev MetricLowerJet (n : ℕ) :=
  Matrix (Fin n) (Fin n) ℝ × (Fin n → Matrix (Fin n) (Fin n) ℝ)

abbrev MetricSecondJet (n : ℕ) := Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ

def lowerJetState (p : MetricLowerJet n) (Q : MetricSecondJet n) : ChartState (n := n) :=
  (p.1, p.2, Q)

def lowerJetSource (background : MetricJet2 (n := n))
    (p : MetricLowerJet n) : Matrix (Fin n) (Fin n) ℝ :=
  chartStateSource background (lowerJetState p 0)

def lowerJetContraction (A : Matrix (Fin n) (Fin n) ℝ)
    (Q : MetricSecondJet n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ a, ∑ b, A a b * Q a b i j

theorem lowerJetContraction_sub_left (A B : Matrix (Fin n) (Fin n) ℝ)
    (Q : MetricSecondJet n) :
    lowerJetContraction (A - B) Q = lowerJetContraction A Q - lowerJetContraction B Q := by
  ext i j
  simp only [lowerJetContraction, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem lowerJetContraction_sub_right (A : Matrix (Fin n) (Fin n) ℝ)
    (Q S : MetricSecondJet n) :
    lowerJetContraction A (Q - S) = lowerJetContraction A Q - lowerJetContraction A S := by
  ext i j
  simp only [lowerJetContraction, Pi.sub_apply, Matrix.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem lowerJetContraction_add_right (A : Matrix (Fin n) (Fin n) ℝ)
    (Q S : MetricSecondJet n) :
    lowerJetContraction A (Q + S) = lowerJetContraction A Q + lowerJetContraction A S := by
  ext i j
  simp only [lowerJetContraction, Pi.add_apply, Matrix.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem norm_lowerJetContraction_le (A : Matrix (Fin n) (Fin n) ℝ)
    (Q : MetricSecondJet n) :
    ‖lowerJetContraction A Q‖ ≤ (n : ℝ) ^ 2 * ‖A‖ * ‖Q‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  have hterm (a b : Fin n) : ‖A a b * Q a b i j‖ ≤ ‖A‖ * ‖Q‖ := by
    rw [norm_mul]
    have hQ : ‖Q a b i j‖ ≤ ‖Q‖ :=
      (Matrix.norm_entry_le_entrywise_sup_norm (Q a b)).trans
        ((norm_le_pi_norm (Q a) b).trans (norm_le_pi_norm Q a))
    exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) hQ
      (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖A a b * Q a b i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
    _ ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖A‖ * ‖Q‖ :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))
    _ = _ := by simp [pow_two, mul_assoc]

theorem contDiff_lowerJetState_zero :
    ContDiff ℝ 1 (fun p : MetricLowerJet n => lowerJetState p 0) := by
  exact contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)

theorem contDiffAt_lowerJetSource (background : MetricJet2 (n := n))
    (p : MetricLowerJet n) (hp : p.1.PosDef) : ContDiffAt ℝ 1 (lowerJetSource background) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact (contDiffAt_chartStateSource background (lowerJetState p 0) hp i j).comp p
    contDiff_lowerJetState_zero.contDiffAt

theorem exists_lowerJet_coefficient_bounds (background : MetricJet2 (n := n))
    (K : Set (MetricLowerJet n)) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef) :
    ∃ LI L0 : NNReal,
      (∀ p ∈ K, ∀ q ∈ K, ‖p.1⁻¹ - q.1⁻¹‖ ≤ (LI : ℝ) * ‖p - q‖) ∧
      (∀ p ∈ K, ∀ q ∈ K,
        ‖lowerJetSource background p - lowerJetSource background q‖ ≤ (L0 : ℝ) * ‖p - q‖) := by
  have hinv : ContDiffOn ℝ 1 (fun p : MetricLowerJet n => p.1⁻¹) K := by
    intro p hp
    have hdet : p.1.det ≠ 0 :=
      (p.1.isUnit_iff_isUnit_det.mp (hpos p hp).isUnit).ne_zero
    exact ((contDiffAt_matrix_inv_of_nonsingular p.1 hdet).comp p
      contDiffAt_fst).contDiffWithinAt
  have hsource : ContDiffOn ℝ 1 (lowerJetSource background) K := by
    intro p hp
    exact (contDiffAt_lowerJetSource background p (hpos p hp)).contDiffWithinAt
  obtain ⟨LI, hLI⟩ := hinv.exists_lipschitzOnWith one_ne_zero hconv hcompact
  obtain ⟨L0, hL0⟩ := hsource.exists_lipschitzOnWith one_ne_zero hconv hcompact
  refine ⟨LI, L0, ?_, ?_⟩
  · intro p hp q hq
    simpa only [dist_eq_norm] using hLI.dist_le_mul p hp q hq
  · intro p hp q hq
    simpa only [dist_eq_norm] using hL0.dist_le_mul p hp q hq

def fixedPrincipalRemainder (background : MetricJet2 (n := n))
    (p : MetricLowerJet n) (Q : MetricSecondJet n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => chartStateSource background (lowerJetState p Q) i j -
    lowerJetContraction background.value⁻¹ Q i j

theorem fixedPrincipalRemainder_split (background : MetricJet2 (n := n))
    (p : MetricLowerJet n) (Q : MetricSecondJet n) (hp : p.1.PosDef)
    (hQm : ∀ a b i j, Q a b i j = Q a b j i)
    (hQd : ∀ a b i j, Q a b i j = Q b a i j) :
    fixedPrincipalRemainder background p Q =
      lowerJetContraction (p.1⁻¹ - background.value⁻¹) Q + lowerJetSource background p := by
  have hG : p.1.IsSymm := by
    simpa only [Matrix.isHermitian_iff_isSymm] using hp.isHermitian
  ext i j
  have hsource : chartStateSource background (lowerJetState p Q) i j =
      lowerJetContraction p.1⁻¹ Q i j + lowerJetSource background p i j :=
    ricciDeTurckSource_quasilinear background (chartStateJet (lowerJetState p Q))
      hG (p.1.isUnit_iff_isUnit_det.mp hp.isUnit).ne_zero hQm hQd i j
  change chartStateSource background (lowerJetState p Q) i j -
      lowerJetContraction background.value⁻¹ Q i j = _
  rw [lowerJetContraction_sub_left, Matrix.add_apply, Matrix.sub_apply, hsource]
  ring

theorem fixedPrincipalRemainder_sub (background : MetricJet2 (n := n))
    (p q : MetricLowerJet n) (Q S : MetricSecondJet n)
    (hp : p.1.PosDef) (hq : q.1.PosDef)
    (hQm : ∀ a b i j, Q a b i j = Q a b j i)
    (hQd : ∀ a b i j, Q a b i j = Q b a i j)
    (hSm : ∀ a b i j, S a b i j = S a b j i)
    (hSd : ∀ a b i j, S a b i j = S b a i j) :
    fixedPrincipalRemainder background p Q - fixedPrincipalRemainder background q S =
      lowerJetContraction (p.1⁻¹ - background.value⁻¹) (Q - S) +
        lowerJetContraction (p.1⁻¹ - q.1⁻¹) S +
          (lowerJetSource background p - lowerJetSource background q) := by
  rw [fixedPrincipalRemainder_split background p Q hp hQm hQd,
    fixedPrincipalRemainder_split background q S hq hSm hSd]
  simp only [lowerJetContraction_sub_left, lowerJetContraction_sub_right]
  abel

theorem norm_fixedPrincipalRemainder_sub_le (background : MetricJet2 (n := n))
    (p q : MetricLowerJet n) (Q S : MetricSecondJet n)
    (hp : p.1.PosDef) (hq : q.1.PosDef)
    (hQm : ∀ a b i j, Q a b i j = Q a b j i)
    (hQd : ∀ a b i j, Q a b i j = Q b a i j)
    (hSm : ∀ a b i j, S a b i j = S a b j i)
    (hSd : ∀ a b i j, S a b i j = S b a i j)
    {LI L0 : NNReal}
    (hI : ‖p.1⁻¹ - q.1⁻¹‖ ≤ (LI : ℝ) * ‖p - q‖)
    (hL : ‖lowerJetSource background p - lowerJetSource background q‖ ≤
      (L0 : ℝ) * ‖p - q‖) :
    ‖fixedPrincipalRemainder background p Q - fixedPrincipalRemainder background q S‖ ≤
      (n : ℝ) ^ 2 * ‖p.1⁻¹ - background.value⁻¹‖ * ‖Q - S‖ +
        ((L0 : ℝ) + (n : ℝ) ^ 2 * (LI : ℝ) * ‖S‖) * ‖p - q‖ := by
  rw [fixedPrincipalRemainder_sub background p q Q S hp hq hQm hQd hSm hSd]
  calc
    _ ≤ (‖lowerJetContraction (p.1⁻¹ - background.value⁻¹) (Q - S)‖ +
        ‖lowerJetContraction (p.1⁻¹ - q.1⁻¹) S‖) +
          ‖lowerJetSource background p - lowerJetSource background q‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ((n : ℝ) ^ 2 * ‖p.1⁻¹ - background.value⁻¹‖ * ‖Q - S‖ +
        (n : ℝ) ^ 2 * ((LI : ℝ) * ‖p - q‖) * ‖S‖) + (L0 : ℝ) * ‖p - q‖ := by
      apply add_le_add _ hL
      apply add_le_add (norm_lowerJetContraction_le _ _)
      exact (norm_lowerJetContraction_le _ _).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI (sq_nonneg _))
          (norm_nonneg S))
    _ = _ := by ring

theorem exists_fixedPrincipalRemainder_tame (background : MetricJet2 (n := n))
    (K : Set (MetricLowerJet n)) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef) :
    ∃ LI L0 : NNReal, ∀ p ∈ K, ∀ q ∈ K, ∀ Q S : MetricSecondJet n,
      (∀ a b i j, Q a b i j = Q a b j i) →
      (∀ a b i j, Q a b i j = Q b a i j) →
      (∀ a b i j, S a b i j = S a b j i) →
      (∀ a b i j, S a b i j = S b a i j) →
      ‖fixedPrincipalRemainder background p Q - fixedPrincipalRemainder background q S‖ ≤
        (n : ℝ) ^ 2 * ‖p.1⁻¹ - background.value⁻¹‖ * ‖Q - S‖ +
          ((L0 : ℝ) + (n : ℝ) ^ 2 * (LI : ℝ) * ‖S‖) * ‖p - q‖ := by
  obtain ⟨LI, L0, hI, hL⟩ :=
    exists_lowerJet_coefficient_bounds background K hconv hcompact hpos
  refine ⟨LI, L0, ?_⟩
  intro p hp q hq Q S hQm hQd hSm hSd
  exact norm_fixedPrincipalRemainder_sub_le background p q Q S (hpos p hp) (hpos q hq)
    hQm hQd hSm hSd (hI p hp q hq) (hL p hp q hq)

theorem exists_centered_fixedPrincipalRemainder_tame (background : MetricJet2 (n := n))
    (K : Set (MetricLowerJet n)) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef) (p0 : MetricLowerJet n) (hp0 : p0 ∈ K)
    (hbackground : background.value = p0.1) :
    ∃ LI L0 : NNReal, ∀ p ∈ K, ∀ q ∈ K, ∀ Q S : MetricSecondJet n,
      (∀ a b i j, Q a b i j = Q a b j i) →
      (∀ a b i j, Q a b i j = Q b a i j) →
      (∀ a b i j, S a b i j = S a b j i) →
      (∀ a b i j, S a b i j = S b a i j) →
      ‖fixedPrincipalRemainder background p Q - fixedPrincipalRemainder background q S‖ ≤
        ((n : ℝ) ^ 2 * (LI : ℝ) * ‖p - p0‖) * ‖Q - S‖ +
          ((L0 : ℝ) + (n : ℝ) ^ 2 * (LI : ℝ) * ‖S‖) * ‖p - q‖ := by
  obtain ⟨LI, L0, hI, hL⟩ :=
    exists_lowerJet_coefficient_bounds background K hconv hcompact hpos
  refine ⟨LI, L0, ?_⟩
  intro p hp q hq Q S hQm hQd hSm hSd
  have hsmall : ‖p.1⁻¹ - background.value⁻¹‖ ≤ (LI : ℝ) * ‖p - p0‖ := by
    rw [hbackground]
    exact hI p hp p0 hp0
  apply (norm_fixedPrincipalRemainder_sub_le background p q Q S (hpos p hp) (hpos q hq)
    hQm hQd hSm hSd (hI p hp q hq) (hL p hp q hq)).trans
  apply add_le_add_left
  calc
    _ ≤ (n : ℝ) ^ 2 * ((LI : ℝ) * ‖p - p0‖) * ‖Q - S‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (sq_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

def backgroundLowerJet (background : MetricJet2 (n := n)) : MetricLowerJet n :=
  (background.value, background.first)

def perturbationRemainder (background : MetricJet2 (n := n))
    (dp : MetricLowerJet n) (DQ : MetricSecondJet n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => chartStateSource background
    (lowerJetState (backgroundLowerJet background + dp) (background.second + DQ)) i j -
      lowerJetContraction background.value⁻¹ DQ i j

theorem perturbationRemainder_eq (background : MetricJet2 (n := n))
    (dp : MetricLowerJet n) (DQ : MetricSecondJet n) :
    perturbationRemainder background dp DQ =
      fixedPrincipalRemainder background (backgroundLowerJet background + dp)
        (background.second + DQ) + lowerJetContraction background.value⁻¹ background.second := by
  ext i j
  simp only [perturbationRemainder, fixedPrincipalRemainder,
    lowerJetContraction_add_right, Matrix.add_apply]
  ring

theorem perturbationRemainder_sub (background : MetricJet2 (n := n))
    (dp dq : MetricLowerJet n) (DQ DS : MetricSecondJet n) :
    perturbationRemainder background dp DQ - perturbationRemainder background dq DS =
      fixedPrincipalRemainder background (backgroundLowerJet background + dp)
        (background.second + DQ) -
      fixedPrincipalRemainder background (backgroundLowerJet background + dq)
        (background.second + DS) := by
  rw [perturbationRemainder_eq, perturbationRemainder_eq, add_sub_add_right_eq_sub]

theorem exists_perturbationRemainder_tame (background : MetricJet2 (n := n))
    (K : Set (MetricLowerJet n)) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef) (hbase : backgroundLowerJet background ∈ K)
    (hBm : ∀ a b i j, background.second a b i j = background.second a b j i)
    (hBd : ∀ a b i j, background.second a b i j = background.second b a i j) :
    ∃ LI L0 : NNReal, ∀ dp dq : MetricLowerJet n,
      backgroundLowerJet background + dp ∈ K →
      backgroundLowerJet background + dq ∈ K → ∀ DQ DS : MetricSecondJet n,
      (∀ a b i j, DQ a b i j = DQ a b j i) →
      (∀ a b i j, DQ a b i j = DQ b a i j) →
      (∀ a b i j, DS a b i j = DS a b j i) →
      (∀ a b i j, DS a b i j = DS b a i j) →
      ‖perturbationRemainder background dp DQ - perturbationRemainder background dq DS‖ ≤
        ((n : ℝ) ^ 2 * (LI : ℝ) * ‖dp‖) * ‖DQ - DS‖ +
          ((L0 : ℝ) + (n : ℝ) ^ 2 * (LI : ℝ) * ‖background.second + DS‖) * ‖dp - dq‖ := by
  obtain ⟨LI, L0, htame⟩ := exists_centered_fixedPrincipalRemainder_tame background K
    hconv hcompact hpos (backgroundLowerJet background) hbase rfl
  refine ⟨LI, L0, ?_⟩
  intro dp dq hdp hdq DQ DS hQm hQd hSm hSd
  have hsumQm : ∀ a b i j,
      (background.second + DQ) a b i j = (background.second + DQ) a b j i := by
    intro a b i j
    simp only [Pi.add_apply, Matrix.add_apply, hBm a b i j, hQm a b i j]
  have hsumQd : ∀ a b i j,
      (background.second + DQ) a b i j = (background.second + DQ) b a i j := by
    intro a b i j
    simp only [Pi.add_apply, Matrix.add_apply, hBd a b i j, hQd a b i j]
  have hsumSm : ∀ a b i j,
      (background.second + DS) a b i j = (background.second + DS) a b j i := by
    intro a b i j
    simp only [Pi.add_apply, Matrix.add_apply, hBm a b i j, hSm a b i j]
  have hsumSd : ∀ a b i j,
      (background.second + DS) a b i j = (background.second + DS) b a i j := by
    intro a b i j
    simp only [Pi.add_apply, Matrix.add_apply, hBd a b i j, hSd a b i j]
  rw [perturbationRemainder_sub]
  simpa only [add_sub_cancel_left, add_sub_add_left_eq_sub] using
    htame (backgroundLowerJet background + dp) hdp (backgroundLowerJet background + dq) hdq
      (background.second + DQ) (background.second + DS) hsumQm hsumQd hsumSm hsumSd

def symmetricLowerJetBall (p0 : MetricLowerJet n) (r : ℝ) : Set (MetricLowerJet n) :=
  {p | p.1.IsSymm} ∩ Metric.closedBall p0 r

theorem convex_symmetricLowerJetBall (p0 : MetricLowerJet n) (r : ℝ) :
    Convex ℝ (symmetricLowerJetBall p0 r) := by
  have hsymm : Convex ℝ {p : MetricLowerJet n | p.1.IsSymm} := by
    intro p hp q hq a b _ _ _
    exact (hp.smul a).add (hq.smul b)
  exact hsymm.inter (convex_closedBall p0 r)

theorem isCompact_symmetricLowerJetBall (p0 : MetricLowerJet n) (r : ℝ) :
    IsCompact (symmetricLowerJetBall p0 r) := by
  have hclosed : IsClosed {p : MetricLowerJet n | p.1.IsSymm} :=
    isClosed_eq continuous_fst.matrix_transpose continuous_fst
  exact (ProperSpace.isCompact_closedBall p0 r).inter_left hclosed

theorem mem_symmetricLowerJetBall_center (p0 : MetricLowerJet n) {r : ℝ}
    (h0 : p0.1.IsSymm) (hr : 0 ≤ r) : p0 ∈ symmetricLowerJetBall p0 r :=
  ⟨h0, Metric.mem_closedBall_self hr⟩

theorem exists_positive_symmetricLowerJetBall (background : MetricJet2 (n := n))
    (hbackground : background.value.PosDef) :
    ∃ r : ℝ, 0 < r ∧
      ∀ p ∈ symmetricLowerJetBall (backgroundLowerJet background) r, p.1.PosDef := by
  obtain ⟨r, hr, hpos⟩ := exists_uniform_posDef_perturbation
    (fun _ : Unit => background.value) (K := {()})
    (isCompact_singleton : IsCompact ({()} : Set Unit))
    continuous_const.continuousOn (fun _ _ => hbackground)
  refine ⟨r, hr, ?_⟩
  intro p hp
  apply hpos () (mem_singleton ()) p.1 hp.1
  exact (norm_fst_le (p - backgroundLowerJet background)).trans
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.2)

theorem exists_local_perturbationRemainder_tame (background : MetricJet2 (n := n))
    (hbackground : background.value.PosDef)
    (hBm : ∀ a b i j, background.second a b i j = background.second a b j i)
    (hBd : ∀ a b i j, background.second a b i j = background.second b a i j) :
    ∃ r : ℝ, 0 < r ∧ ∃ LI L0 : NNReal,
      (∀ dp : MetricLowerJet n, dp.1.IsSymm → ‖dp‖ ≤ r →
        (background.value + dp.1).PosDef) ∧
      ∀ dp dq : MetricLowerJet n,
        dp.1.IsSymm → dq.1.IsSymm → ‖dp‖ ≤ r → ‖dq‖ ≤ r →
        ∀ DQ DS : MetricSecondJet n,
        (∀ a b i j, DQ a b i j = DQ a b j i) →
        (∀ a b i j, DQ a b i j = DQ b a i j) →
        (∀ a b i j, DS a b i j = DS a b j i) →
        (∀ a b i j, DS a b i j = DS b a i j) →
        ‖perturbationRemainder background dp DQ - perturbationRemainder background dq DS‖ ≤
          ((n : ℝ) ^ 2 * (LI : ℝ) * ‖dp‖) * ‖DQ - DS‖ +
            ((L0 : ℝ) + (n : ℝ) ^ 2 * (LI : ℝ) * ‖background.second + DS‖) *
              ‖dp - dq‖ := by
  obtain ⟨r, hr, hpos⟩ := exists_positive_symmetricLowerJetBall background hbackground
  have hBsymm : background.value.IsSymm := by
    simpa only [Matrix.isHermitian_iff_isSymm] using hbackground.isHermitian
  have hbase : backgroundLowerJet background ∈
      symmetricLowerJetBall (backgroundLowerJet background) r :=
    mem_symmetricLowerJetBall_center _ hBsymm hr.le
  obtain ⟨LI, L0, htame⟩ := exists_perturbationRemainder_tame background
    (symmetricLowerJetBall (backgroundLowerJet background) r)
    (convex_symmetricLowerJetBall _ _) (isCompact_symmetricLowerJetBall _ _)
    hpos hbase hBm hBd
  have hmem (dp : MetricLowerJet n) (hsymm : dp.1.IsSymm) (hsmall : ‖dp‖ ≤ r) :
      backgroundLowerJet background + dp ∈
        symmetricLowerJetBall (backgroundLowerJet background) r := by
    refine ⟨hBsymm.add hsymm, ?_⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hsmall
  refine ⟨r, hr, LI, L0, ?_, ?_⟩
  · intro dp hsymm hsmall
    exact hpos _ (hmem dp hsymm hsmall)
  · intro dp dq hdp hdq hp hq DQ DS hQm hQd hSm hSd
    exact htame dp dq (hmem dp hdp hp) (hmem dq hdq hq) DQ DS hQm hQd hSm hSd

theorem exists_small_principal_perturbationRemainder (background : MetricJet2 (n := n))
    (hbackground : background.value.PosDef)
    (hBm : ∀ a b i j, background.second a b i j = background.second a b j i)
    (hBd : ∀ a b i j, background.second a b i j = background.second b a i j)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ r : ℝ, 0 < r ∧ ∃ LI L0 : NNReal,
      (∀ dp : MetricLowerJet n, dp.1.IsSymm → ‖dp‖ ≤ r →
        (background.value + dp.1).PosDef) ∧
      ∀ dp dq : MetricLowerJet n,
        dp.1.IsSymm → dq.1.IsSymm → ‖dp‖ ≤ r → ‖dq‖ ≤ r →
        ∀ DQ DS : MetricSecondJet n,
        (∀ a b i j, DQ a b i j = DQ a b j i) →
        (∀ a b i j, DQ a b i j = DQ b a i j) →
        (∀ a b i j, DS a b i j = DS a b j i) →
        (∀ a b i j, DS a b i j = DS b a i j) →
        ‖perturbationRemainder background dp DQ - perturbationRemainder background dq DS‖ ≤
          eps * ‖DQ - DS‖ +
            ((L0 : ℝ) + (n : ℝ) ^ 2 * (LI : ℝ) * ‖background.second + DS‖) *
              ‖dp - dq‖ := by
  obtain ⟨r0, hr0, LI, L0, hpos, htame⟩ :=
    exists_local_perturbationRemainder_tame background hbackground hBm hBd
  let C : ℝ := (n : ℝ) ^ 2 * (LI : ℝ)
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) LI.coe_nonneg
  have hden : 0 < 1 + C := by linarith
  let r : ℝ := min r0 (eps / (1 + C))
  have hr : 0 < r := lt_min hr0 (div_pos heps hden)
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hsmall {dp : MetricLowerJet n} (hdp : ‖dp‖ ≤ r) : C * ‖dp‖ ≤ eps := by
    have hp : ‖dp‖ ≤ eps / (1 + C) := hdp.trans (min_le_right _ _)
    have hmul : ‖dp‖ * (1 + C) ≤ eps := (le_div_iff₀ hden).mp hp
    nlinarith [norm_nonneg dp]
  refine ⟨r, hr, LI, L0, ?_, ?_⟩
  · intro dp hsymm hdp
    exact hpos dp hsymm (hdp.trans hrr0)
  · intro dp dq hdp hdq hp hq DQ DS hQm hQd hSm hSd
    exact (htame dp dq hdp hdq (hp.trans hrr0) (hq.trans hrr0)
      DQ DS hQm hQd hSm hSd).trans
      (add_le_add_left (mul_le_mul_of_nonneg_right (hsmall hp) (norm_nonneg _)) _)

section IntegratedRemainder

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

theorem continuous_lowerJetContraction :
    Continuous (fun q : Matrix (Fin n) (Fin n) ℝ × MetricSecondJet n =>
      lowerJetContraction q.1 q.2) := by
  unfold lowerJetContraction
  fun_prop

theorem aestronglyMeasurable_fixedPrincipalRemainder
    (background : MetricJet2 (n := n)) {p : X → MetricLowerJet n}
    (hp : Continuous p) (hpos : ∀ x, (p x).1.PosDef)
    {Q : X → MetricSecondJet n} (hQ : AEStronglyMeasurable Q μ)
    (hQm : ∀ x a b i j, Q x a b i j = Q x a b j i)
    (hQd : ∀ x a b i j, Q x a b i j = Q x b a i j) :
    AEStronglyMeasurable (fun x => fixedPrincipalRemainder background (p x) (Q x)) μ := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin n → Fin n → ℝ))
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  have hinv : Continuous (fun x => (p x).1⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (continuousAt_matrix_inv_of_posDef (p x).1 (hpos x)).comp
      (f := fun y : X => (p y).1) (hp.fst.continuousAt (x := x))
  have hsource : Continuous (fun x => lowerJetSource background (p x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_lowerJetSource background (p x) (hpos x)).continuousAt.comp
      (f := p) (hp.continuousAt (x := x))
  have hcoeff : Continuous (fun x => (p x).1⁻¹ - background.value⁻¹) :=
    hinv.sub continuous_const
  have hcoeffAE : AEStronglyMeasurable
      (fun x => (p x).1⁻¹ - background.value⁻¹) μ := hcoeff.aestronglyMeasurable
  have hprod := (continuous_lowerJetContraction (n := n)).comp_aestronglyMeasurable
    (hcoeffAE.prodMk hQ)
  have heq : (fun x => fixedPrincipalRemainder background (p x) (Q x)) =
      fun x => lowerJetContraction ((p x).1⁻¹ - background.value⁻¹) (Q x) +
        lowerJetSource background (p x) := by
    funext x
    exact fixedPrincipalRemainder_split background (p x) (Q x) (hpos x) (hQm x) (hQd x)
  rw [heq]
  exact hprod.add hsource.aestronglyMeasurable

theorem aestronglyMeasurable_perturbationRemainder
    (background : MetricJet2 (n := n)) {dp : X → MetricLowerJet n}
    (hp : Continuous dp) (hpos : ∀ x, (background.value + (dp x).1).PosDef)
    {Q : X → MetricSecondJet n} (hQ : AEStronglyMeasurable Q μ)
    (hBm : ∀ a b i j, background.second a b i j = background.second a b j i)
    (hBd : ∀ a b i j, background.second a b i j = background.second b a i j)
    (hQm : ∀ x a b i j, Q x a b i j = Q x a b j i)
    (hQd : ∀ x a b i j, Q x a b i j = Q x b a i j) :
    AEStronglyMeasurable (fun x => perturbationRemainder background (dp x) (Q x)) μ := by
  have hm : AEStronglyMeasurable (fun x => fixedPrincipalRemainder background
      (backgroundLowerJet background + dp x) (background.second + Q x)) μ :=
    aestronglyMeasurable_fixedPrincipalRemainder μ background (continuous_const.add hp)
      hpos (aestronglyMeasurable_const.add hQ)
      (by intro x a b i j; simp only [Pi.add_apply, Matrix.add_apply, hBm, hQm])
      (by intro x a b i j; simp only [Pi.add_apply, Matrix.add_apply, hBd, hQd])
  have heq : (fun x => perturbationRemainder background (dp x) (Q x)) =
      fun x => fixedPrincipalRemainder background (backgroundLowerJet background + dp x)
        (background.second + Q x) + lowerJetContraction background.value⁻¹ background.second := by
    funext x
    exact perturbationRemainder_eq background (dp x) (Q x)
  rw [heq]
  exact hm.add aestronglyMeasurable_const

private theorem lpNorm_const_mul_norm {V : Type*} [NormedAddCommGroup V]
    {f : X → V} (hf : AEStronglyMeasurable f μ) {c : ℝ} (hc : 0 ≤ c) :
    lpNorm (fun x => c * ‖f x‖) 2 μ = c * lpNorm f 2 μ := by
  change lpNorm (c • (fun x => ‖f x‖)) 2 μ = _
  rw [lpNorm_const_smul, lpNorm_norm hf]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc]

theorem memLp_lpNorm_le_three
    {V V₁ V₂ V₃ : Type*} [NormedAddCommGroup V] [NormedAddCommGroup V₁]
    [NormedAddCommGroup V₂] [NormedAddCommGroup V₃]
    {f : X → V} (hf : AEStronglyMeasurable f μ)
    {f₁ : X → V₁} {f₂ : X → V₂} {f₃ : X → V₃}
    (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ) (h₃ : MemLp f₃ 2 μ)
    {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hbound : ∀ x, ‖f x‖ ≤ c₁ * ‖f₁ x‖ + c₂ * ‖f₂ x‖ + c₃ * ‖f₃ x‖) :
    MemLp f 2 μ ∧ lpNorm f 2 μ ≤
      c₁ * lpNorm f₁ 2 μ + c₂ * lpNorm f₂ 2 μ + c₃ * lpNorm f₃ 2 μ := by
  let H₁ : X → ℝ := fun x => c₁ * ‖f₁ x‖
  let H₂ : X → ℝ := fun x => c₂ * ‖f₂ x‖
  let H₃ : X → ℝ := fun x => c₃ * ‖f₃ x‖
  have hH₁ : MemLp H₁ 2 μ := h₁.norm.const_mul c₁
  have hH₂ : MemLp H₂ 2 μ := h₂.norm.const_mul c₂
  have hH₃ : MemLp H₃ 2 μ := h₃.norm.const_mul c₃
  have hH : MemLp (H₁ + H₂ + H₃) 2 μ := (hH₁.add hH₂).add hH₃
  have hnonneg (x : X) : 0 ≤ (H₁ + H₂ + H₃) x :=
    add_nonneg (add_nonneg (mul_nonneg hc₁ (norm_nonneg _))
      (mul_nonneg hc₂ (norm_nonneg _))) (mul_nonneg hc₃ (norm_nonneg _))
  refine ⟨hH.of_le hf (Eventually.of_forall (fun x => ?_)), ?_⟩
  · change ‖f x‖ ≤ ‖(H₁ + H₂ + H₃) x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    exact hbound x
  · calc
      _ ≤ lpNorm (H₁ + H₂ + H₃) 2 μ := lpNorm_mono_real hH hbound
      _ ≤ (lpNorm H₁ 2 μ + lpNorm H₂ 2 μ) + lpNorm H₃ 2 μ :=
        (lpNorm_add_le (hH₁.add hH₂) (by norm_num)).trans
          (add_le_add (lpNorm_add_le (g := H₂) hH₁ (by norm_num)) le_rfl)
      _ = _ := by
        rw [lpNorm_const_mul_norm μ h₁.aestronglyMeasurable hc₁,
          lpNorm_const_mul_norm μ h₂.aestronglyMeasurable hc₂,
          lpNorm_const_mul_norm μ h₃.aestronglyMeasurable hc₃]

theorem exists_small_principal_L2_remainder (background : MetricJet2 (n := n))
    (hbackground : background.value.PosDef)
    (hBm : ∀ a b i j, background.second a b i j = background.second a b j i)
    (hBd : ∀ a b i j, background.second a b i j = background.second b a i j)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ r : ℝ, 0 < r ∧ ∃ LI L0 : NNReal,
      ∀ (dp dq : X → MetricLowerJet n) (Q S : X → MetricSecondJet n),
      Continuous dp → Continuous dq →
      (∀ x, (dp x).1.IsSymm) → (∀ x, (dq x).1.IsSymm) →
      (∀ x, ‖dp x‖ ≤ r) → (∀ x, ‖dq x‖ ≤ r) →
      (∀ x a b i j, Q x a b i j = Q x a b j i) →
      (∀ x a b i j, Q x a b i j = Q x b a i j) →
      (∀ x a b i j, S x a b i j = S x a b j i) →
      (∀ x a b i j, S x a b i j = S x b a i j) →
      MemLp (fun x => Q x - S x) 2 μ → MemLp (fun x => dp x - dq x) 2 μ →
      MemLp (fun x => background.second + S x) 2 μ →
      ∀ b : ℝ, 0 ≤ b → (∀ x, ‖dp x - dq x‖ ≤ b) →
      MemLp (fun x => perturbationRemainder background (dp x) (Q x) -
        perturbationRemainder background (dq x) (S x)) 2 μ ∧
      lpNorm (fun x => perturbationRemainder background (dp x) (Q x) -
        perturbationRemainder background (dq x) (S x)) 2 μ ≤
        eps * lpNorm (fun x => Q x - S x) 2 μ +
          (L0 : ℝ) * lpNorm (fun x => dp x - dq x) 2 μ +
          ((n : ℝ) ^ 2 * (LI : ℝ) * b) *
            lpNorm (fun x => background.second + S x) 2 μ := by
  obtain ⟨r, hr, LI, L0, hpos, htame⟩ :=
    exists_small_principal_perturbationRemainder background hbackground hBm hBd heps
  refine ⟨r, hr, LI, L0, ?_⟩
  intro dp dq Q S hp hq hps hqs hpr hqr hQm hQd hSm hSd hQS hpq hBS b hb hbpq
  have hS : AEStronglyMeasurable S μ := by
    have h := hBS.aestronglyMeasurable.sub
      (aestronglyMeasurable_const (b := background.second))
    exact h.congr (Eventually.of_forall (fun x => by
      change background.second + S x - background.second = S x
      abel))
  have hQ : AEStronglyMeasurable Q μ := by
    have h := hQS.aestronglyMeasurable.add hS
    exact h.congr (Eventually.of_forall (fun x => sub_add_cancel (Q x) (S x)))
  have hR := (aestronglyMeasurable_perturbationRemainder μ background hp
    (fun x => hpos (dp x) (hps x) (hpr x)) hQ hBm hBd hQm hQd).sub
    (aestronglyMeasurable_perturbationRemainder μ background hq
      (fun x => hpos (dq x) (hqs x) (hqr x)) hS hBm hBd hSm hSd)
  apply memLp_lpNorm_le_three μ hR hQS hpq hBS heps.le L0.coe_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) LI.coe_nonneg) hb)
  intro x
  have ht := htame (dp x) (dq x) (hps x) (hqs x) (hpr x) (hqr x)
    (Q x) (S x) (hQm x) (hQd x) (hSm x) (hSd x)
  have hcross := mul_le_mul_of_nonneg_left (hbpq x)
    (mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) LI.coe_nonneg)
      (norm_nonneg (background.second + S x)))
  simp only [Pi.sub_apply]
  nlinarith only [ht, hcross]

end IntegratedRemainder

end PoincareConjecture.DeTurckNative
