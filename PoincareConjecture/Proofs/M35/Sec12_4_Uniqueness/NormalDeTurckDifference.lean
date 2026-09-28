import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.NormalDeTurckJet









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness

open DeTurckNative

variable {n : ℕ}

theorem contDiffAt_normalLowerJetSource
    (z : (Fin n → Fin n → Fin n → Fin n → ℝ) × MetricLowerJet n)
    (hz : z.2.1.PosDef) :
    ContDiffAt ℝ 1 (fun w => normalLowerJetSource w.1 w.2) z := by
  have hlow := (contDiffAt_lowerJetSource flatMetricJet z.2 hz).comp z
    contDiffAt_snd
  have hinv : ContDiffAt ℝ 1 (fun w :
      (Fin n → Fin n → Fin n → Fin n → ℝ) × MetricLowerJet n => w.2.1⁻¹) z :=
    (contDiffAt_matrix_inv_of_nonsingular z.2.1
      (z.2.1.isUnit_iff_isUnit_det.mp hz.isUnit).ne_zero).comp z
        (contDiffAt_fst.comp z contDiffAt_snd)
  have hv (i j : Fin n) : ContDiffAt ℝ 1 (fun w :
      (Fin n → Fin n → Fin n → Fin n → ℝ) × MetricLowerJet n => w.2.1 i j) z := by
    fun_prop
  have hr (a i c k : Fin n) : ContDiffAt ℝ 1 (fun w :
      (Fin n → Fin n → Fin n → Fin n → ℝ) × MetricLowerJet n => w.1 a i c k) z := by
    fun_prop
  have hcurv : ContDiffAt ℝ 1 (fun w => normalCurvatureSource w.1 w.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    apply ContDiffAt.sum
    intro k _
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro c _
    exact (contDiffAt_pi.mp (contDiffAt_pi.mp hinv a) c).mul
      (((hv k j).mul (hr a i c k)).add ((hv i k).mul (hr a j c k)))
  exact hlow.add hcurv

theorem exists_normalLowerJetSource_lipschitz
    (K : Set (MetricLowerJet n)) (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (hKpos : ∀ p ∈ K, p.1.PosDef) (R : ℝ) :
    ∃ L : NNReal, ∀ C : Fin n → Fin n → Fin n → Fin n → ℝ, ‖C‖ ≤ R →
      ∀ p ∈ K, ∀ q ∈ K,
      ‖normalLowerJetSource C p - normalLowerJetSource C q‖ ≤ (L : ℝ) * ‖p - q‖ := by
  let B : Set (Fin n → Fin n → Fin n → Fin n → ℝ) := Metric.closedBall 0 R
  have hs : ContDiffOn ℝ 1 (fun z => normalLowerJetSource z.1 z.2) (B ×ˢ K) := by
    intro z hz
    exact (contDiffAt_normalLowerJetSource z (hKpos z.2 hz.2)).contDiffWithinAt
  obtain ⟨L, hL⟩ := hs.exists_lipschitzOnWith one_ne_zero
    ((convex_closedBall (0 : Fin n → Fin n → Fin n → Fin n → ℝ) R).prod hKconv)
    ((isCompact_closedBall _ _).prod hKcompact)
  refine ⟨L, ?_⟩
  intro C hC p hp q hq
  have hCB : C ∈ B := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hC
  simpa [dist_eq_norm, Prod.norm_def] using
    hL.dist_le_mul (C, p) ⟨hCB, hp⟩ (C, q) ⟨hCB, hq⟩




theorem native_normal_covariant_difference (b p q : MetricJet2 (n := n))
    (hb : b.first = 0)
    (hbs : ∀ a c i j, b.second a c i j = b.second a c j i)
    (hp : p.value.PosDef) (hq : q.value.PosDef)
    (hpm : ∀ a c i j, p.second a c i j = p.second a c j i)
    (hpd : ∀ a c i j, p.second a c i j = p.second c a i j)
    (hqm : ∀ a c i j, q.second a c i j = q.second a c j i)
    (hqd : ∀ a c i j, q.second a c i j = q.second c a i j) (i j : Fin n) :
    ricciDeTurckSource b p i j - ricciDeTurckSource b q i j -
        lowerJetContraction p.value⁻¹
          (normalCovariantSecondJet b p - normalCovariantSecondJet b q) i j =
      lowerJetContraction (p.value⁻¹ - q.value⁻¹) (normalCovariantSecondJet b q) i j +
        (normalLowerJetSource (mixedCurvatureJet b) (p.value, p.first) i j -
          normalLowerJetSource (mixedCurvatureJet b) (q.value, q.first) i j) := by
  rw [native_source_normal_covariant b p hb hbs hp hpm hpd,
    native_source_normal_covariant b q hb hbs hq hqm hqd,
    lowerJetContraction_sub_left, lowerJetContraction_sub_right]
  simp only [Matrix.sub_apply]
  ring



theorem exists_normal_covariant_difference_bound
    (K : Set (MetricLowerJet n)) (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (hKpos : ∀ p ∈ K, p.1.PosDef) {H R : ℝ} (hH : 0 ≤ H) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ b p q : MetricJet2 (n := n),
      b.first = 0 →
      (∀ a c i j, b.second a c i j = b.second a c j i) →
      ‖mixedCurvatureJet b‖ ≤ R →
      (p.value, p.first) ∈ K → (q.value, q.first) ∈ K →
      (∀ a c i j, p.second a c i j = p.second a c j i) →
      (∀ a c i j, p.second a c i j = p.second c a i j) →
      (∀ a c i j, q.second a c i j = q.second a c j i) →
      (∀ a c i j, q.second a c i j = q.second c a i j) →
      ‖normalCovariantSecondJet b q‖ ≤ H →
      ‖(fun i j => ricciDeTurckSource b p i j - ricciDeTurckSource b q i j -
        lowerJetContraction p.value⁻¹
          (normalCovariantSecondJet b p - normalCovariantSecondJet b q) i j :
          Matrix (Fin n) (Fin n) ℝ)‖ ≤ D * ‖(p.value, p.first) - (q.value, q.first)‖ := by
  obtain ⟨LI, _, hI, _⟩ := exists_lowerJet_coefficient_bounds flatMetricJet
    K hKconv hKcompact hKpos
  obtain ⟨L, hL⟩ := exists_normalLowerJetSource_lipschitz K hKconv hKcompact hKpos R
  refine ⟨(n : ℝ) ^ 2 * (LI : ℝ) * H + L, by positivity, ?_⟩
  intro b p q hb hbs hbR hp hq hpm hpd hqm hqd hS
  have heq : (fun i j => ricciDeTurckSource b p i j - ricciDeTurckSource b q i j -
      lowerJetContraction p.value⁻¹
        (normalCovariantSecondJet b p - normalCovariantSecondJet b q) i j :
      Matrix (Fin n) (Fin n) ℝ) =
      lowerJetContraction (p.value⁻¹ - q.value⁻¹) (normalCovariantSecondJet b q) +
        (normalLowerJetSource (mixedCurvatureJet b) (p.value, p.first) -
          normalLowerJetSource (mixedCurvatureJet b) (q.value, q.first)) := by
    ext i j
    exact native_normal_covariant_difference b p q hb hbs
      (hKpos _ hp) (hKpos _ hq) hpm hpd hqm hqd i j
  have hlow : ‖normalLowerJetSource (mixedCurvatureJet b) (p.value, p.first) -
      normalLowerJetSource (mixedCurvatureJet b) (q.value, q.first)‖ ≤
      (L : ℝ) * ‖(p.value, p.first) - (q.value, q.first)‖ := by
    exact hL (mixedCurvatureJet b) hbR _ hp _ hq
  have hinv : ‖p.value⁻¹ - q.value⁻¹‖ ≤
      (LI : ℝ) * ‖(p.value, p.first) - (q.value, q.first)‖ :=
    hI (p.value, p.first) hp (q.value, q.first) hq
  rw [heq]
  calc
    _ ≤ ‖lowerJetContraction (p.value⁻¹ - q.value⁻¹) (normalCovariantSecondJet b q)‖ +
        ‖normalLowerJetSource (mixedCurvatureJet b) (p.value, p.first) -
          normalLowerJetSource (mixedCurvatureJet b) (q.value, q.first)‖ := norm_add_le _ _
    _ ≤ (n : ℝ) ^ 2 * ((LI : ℝ) * ‖(p.value, p.first) - (q.value, q.first)‖) * H +
        (L : ℝ) * ‖(p.value, p.first) - (q.value, q.first)‖ := by
      apply add_le_add _ hlow
      exact (norm_lowerJetContraction_le _ _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hinv (sq_nonneg _))
          hS (norm_nonneg _) (by positivity))
    _ = _ := by ring

end PoincareConjecture.M35.Uniqueness
