import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.TimeDerivatives
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.MixedJets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology RealInnerProductSpace

namespace Poincare.Parabolic.Interior

variable {n : ℕ} [NeZero n]
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_static_heat_mixed_jet_bound
    {lam Λ H : ℝ} (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H)
    {r R α β a b : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hα : α < a) (hab : a ≤ b) (hβ : b < β)
    (A : E → E →L[ℝ] E) (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 R))
    (hsym : ∀ x ∈ Metric.ball 0 R, ∀ v w,
      inner ℝ (A x v) w = inner ℝ v (A x w))
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v) ∧ inner ℝ v (A x v) ≤ Λ * ‖v‖ ^ 2)
    (hholder : ∀ x ∈ Metric.ball 0 R, ∀ y ∈ Metric.ball 0 R,
      ‖A x - A y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ f : E × ℝ → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 R ×ˢ Ioo α β) →
      (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β,
        timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
          (spatialDerivative (spatialDerivative f) (x, t))) →
      (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β, |f (x, t)| ≤ B) →
      ∀ x ∈ Metric.closedBall 0 r, ∀ t ∈ Icc a b,
        ‖iteratedFDeriv ℝ i (fun z => ((timeDerivative^[j]) f) (z, t)) x‖ ≤ C * B := by
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hs : 0 ≤ s := hr.trans hrs.le
  have hclosure : closure (Metric.ball (0 : E) s) ⊆ Metric.closedBall 0 s :=
    closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  have hVc : IsCompact (closure (Metric.ball (0 : E) s)) :=
    (isCompact_closedBall 0 s).of_isClosed_subset isClosed_closure hclosure
  have hVO : closure (Metric.ball (0 : E) s) ⊆ Metric.ball 0 R :=
    fun x hx => (hclosure hx).trans_lt hsR
  have hKV : Metric.closedBall (0 : E) r ⊆ Metric.ball 0 s :=
    fun x hx => hx.trans_lt hrs
  have hma : ∀ i j, ContDiffOn ℝ ∞ (fun x => coefficientMatrix (A x) i j)
      (Metric.ball 0 R) := by
    intro i j
    simp only [coefficientMatrix_apply]
    exact ContDiffOn.inner ℝ contDiffOn_const (hA.clm_apply contDiffOn_const)
  obtain ⟨q, C₀, hC₀, hspace⟩ := exists_spatial_jet_bound_of_bounded_powers
    Metric.isOpen_ball Metric.isOpen_ball hVc hVO (isCompact_closedBall 0 r) hKV
    (fun z => coefficientMatrix (A z)) (fun _ _ => 0) hma
    (fun x hx => coefficientMatrix_posDef (A x) (hsym x hx) hlam (fun v => (hell x hx v).1))
    (fun _ => contDiffOn_const) i
  choose T hT htime using fun l : ℕ => exists_uniform_iterate_timeDerivative_bound_on
    n (NeZero.pos n) hlam hlamΛ hH (j + l) s R α β a b hs hsR hα hab hβ
  let Q : ℝ := ∑ l ∈ Finset.range (q + 1), T l
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun l _ => (hT l).le)
  refine ⟨C₀ * (Q + 1), mul_pos hC₀ (by positivity), ?_⟩
  intro B hB f hf hheat hvalue x hx t ht
  have htJ : t ∈ Ioo α β := ⟨hα.trans_le ht.1, ht.2.trans_lt hβ⟩
  have hiter := iterate_timeDerivative_static_heat_equation_on
    Metric.isOpen_ball isOpen_Ioo hf hheat j
  have hslice : ContDiffOn ℝ ∞ (fun z => ((timeDerivative^[j]) f) (z, t)) (Metric.ball 0 R) :=
    hiter.1.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, htJ⟩)
  have hpowers : ∀ l ≤ q, ∀ z ∈ Metric.ball (0 : E) s,
      |((Analysis.Elliptic.InteriorEstimates.secondOrderOperator
          (fun z => coefficientMatrix (A z)) (fun _ _ => 0))^[l]
        (fun z => ((timeDerivative^[j]) f) (z, t))) z| ≤ (Q + 1) * B := by
    intro l hl z hz
    rw [iterate_secondOrderOperator_timeDerivative_slice_on
      Metric.isOpen_ball isOpen_Ioo hf hheat j l htJ (hz.trans hsR)]
    have he := htime l A hA hsym hell hholder B hB f hf hheat hvalue
      z (Metric.ball_subset_closedBall hz) t ht
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ hB
    exact (Finset.single_le_sum (fun l _ => (hT l).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))).trans (le_add_of_nonneg_right zero_le_one)
  simpa only [mul_assoc] using
    hspace ((Q + 1) * B) (mul_nonneg (by positivity) hB) hslice hpowers x hx

theorem exists_static_heat_spacetime_jet_bound
    {lam Λ H : ℝ} (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H)
    {r R α β a b : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hα : α < a) (hab : a ≤ b) (hβ : b < β)
    (A : E → E →L[ℝ] E) (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 R))
    (hsym : ∀ x ∈ Metric.ball 0 R, ∀ v w,
      inner ℝ (A x v) w = inner ℝ v (A x w))
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v) ∧ inner ℝ v (A x v) ≤ Λ * ‖v‖ ^ 2)
    (hholder : ∀ x ∈ Metric.ball 0 R, ∀ y ∈ Metric.ball 0 R,
      ‖A x - A y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ f : E × ℝ → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 R ×ˢ Ioo α β) →
      (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β,
        timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
          (spatialDerivative (spatialDerivative f) (x, t))) →
      (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β, |f (x, t)| ≤ B) →
      ∀ p ∈ Metric.closedBall (0 : E) r ×ˢ Icc a b,
        ‖iteratedFDeriv ℝ m f p‖ ≤ C * B := by
  choose C hC hbound using fun i j : ℕ => exists_static_heat_mixed_jet_bound
    hlam hlamΛ hH hr hrR hα hab hβ A hA hsym hell hholder i j
  let Q : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), C i (m - i)
  have hQ : 0 < Q := by
    have hs : 0 ≤ ∑ i ∈ Finset.range (m + 1), C i (m - i) :=
      Finset.sum_nonneg (fun i _ => (hC i (m - i)).le)
    dsimp [Q]
    linarith
  refine ⟨2 ^ m * Q, by positivity, ?_⟩
  intro B hB f hf hheat hvalue p hp
  have hpU : p ∈ Metric.ball 0 R ×ˢ Ioo α β :=
    ⟨hp.1.trans_lt hrR, hα.trans_le hp.2.1, hp.2.2.trans_lt hβ⟩
  apply (norm_iteratedFDeriv_le_of_mixed_bounds_on
    (Metric.isOpen_ball.prod isOpen_Ioo) hf m p hpU (B := Q * B) ?_).trans_eq
      (mul_assoc _ _ _).symm
  intro i j hij
  apply (hbound i j B hB f hf hheat hvalue p.1 hp.1 p.2 hp.2).trans
  apply mul_le_mul_of_nonneg_right _ hB
  have hji : j = m - i := by omega
  rw [hji]
  exact (Finset.single_le_sum (fun l _ => (hC l (m - l)).le)
    (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)

end Poincare.Parabolic.Interior
