import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.TimeDerivatives.Equation
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.RescaledEstimate




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior



theorem exists_uniform_static_heat_timeDerivative_bound
    (n : ℕ) (hn : 1 ≤ n) {r δ lam Λ H : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
        ContDiffOn ℝ ∞ a (Metric.ball x (2 * r)) →
        (∀ y ∈ Metric.ball x (2 * r), ∀ v w,
          inner ℝ (a y v) w = inner ℝ v (a y w)) →
        (∀ y ∈ Metric.ball x (2 * r), ∀ v,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (a y v) ∧
          inner ℝ v (a y v) ≤ Λ * ‖v‖ ^ 2) →
        (∀ y ∈ Metric.ball x (2 * r), ∀ z ∈ Metric.ball x (2 * r),
          ‖a y - a z‖ ≤ H * ‖y - z‖ ^ (1 / 2 : ℝ)) →
        ∀ (B : ℝ), 0 ≤ B →
        ∀ (f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ), ContDiff ℝ ∞ f →
          (∀ y ∈ Metric.ball x (2 * r), ∀ s ∈ Ioo (t - δ) (t + δ),
            timeDerivative f (y, s) = Kernel.matrixLap (coefficientMatrix (a y))
              (spatialDerivative (spatialDerivative f) (y, s))) →
          (∀ y ∈ Metric.ball x (2 * r), ∀ s ∈ Ioc (t - δ) t, |f (y, s)| ≤ B) →
          |timeDerivative f (x, t)| ≤ C * B := by
  obtain ⟨C, hC, hest⟩ := Poincare.Parabolic.exists_uniform_interior_heat_hessian_bound_scaled
    n hn hr (mul_pos hδ hlam) (mul_le_mul_of_nonneg_left hlamΛ hδ.le)
      (mul_nonneg hδ.le hH)
  refine ⟨(n : ℝ) ^ 2 * Λ * C, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hΛ : 0 < Λ := hlam.trans_le hlamΛ
    positivity, ?_⟩
  intro a x t ha hsym hell hholder B hB f hf hheat hb
  let b := fun y => δ • a (y + x)
  let u := fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
    f (p.1 + x, t + δ * (p.2 - 1))
  have hmem {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.ball 0 (r * 2)) :
      y + x ∈ Metric.ball x (2 * r) := by
    simpa [Metric.mem_ball, dist_eq_norm, mul_comm] using hy
  have htime {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
      t + δ * (s - 1) ∈ Ioc (t - δ) t := by
    constructor
    · nlinarith [mul_pos hδ hs.1]
    · nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hs.2)]
  have htime' {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
      t + δ * (s - 1) ∈ Ioo (t - δ) (t + δ) :=
    ⟨(htime hs).1, (htime hs).2.trans_lt (by linarith)⟩
  have hbs : ContDiffOn ℝ ∞ b (Metric.ball 0 (r * 2)) :=
    (ha.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy => hmem hy)).const_smul δ
  have hsymb : ∀ y ∈ Metric.ball 0 (r * 2), ∀ v w,
      inner ℝ (b y v) w = inner ℝ v (b y w) := by
    intro y hy v w
    simpa only [b, smul_apply, real_inner_smul_left, real_inner_smul_right] using
      congrArg (δ * ·) (hsym _ (hmem hy) v w)
  have hellb : ∀ y ∈ Metric.ball 0 (r * 2), ∀ v,
      (δ * lam) * ‖v‖ ^ 2 ≤ inner ℝ v (b y v) ∧
      inner ℝ v (b y v) ≤ (δ * Λ) * ‖v‖ ^ 2 := by
    intro y hy v
    simpa only [b, smul_apply, real_inner_smul_right, mul_assoc] using
      And.intro (mul_le_mul_of_nonneg_left (hell _ (hmem hy) v).1 hδ.le)
        (mul_le_mul_of_nonneg_left (hell _ (hmem hy) v).2 hδ.le)
  have hholderb : ∀ y ∈ Metric.ball 0 (r * 2), ∀ z ∈ Metric.ball 0 (r * 2),
      ‖b y - b z‖ ≤ (δ * H) * ‖y - z‖ ^ (1 / 2 : ℝ) := by
    intro y hy z hz
    dsimp only [b]
    rw [← smul_sub δ (a (y + x)) (a (z + x)), norm_smul, Real.norm_of_nonneg hδ.le]
    simpa only [
      add_sub_add_right_eq_sub, mul_assoc] using
      mul_le_mul_of_nonneg_left (hholder _ (hmem hy) _ (hmem hz)) hδ.le
  have hu : ContDiff ℝ ∞ u :=
    hf.comp ((contDiff_fst.add contDiff_const).prodMk
      (contDiff_const.add (contDiff_const.mul (contDiff_snd.sub contDiff_const))))
  have hujet (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
      fderiv ℝ (fderiv ℝ (fun z => u (z, s))) y =
        spatialDerivative (spatialDerivative f) (y + x, t + δ * (s - 1)) := by
    have hfirst : fderiv ℝ (fun z => u (z, s)) =
        (fun z => fderiv ℝ (fun z => f (z, t + δ * (s - 1))) (z + x)) := by
      funext z
      exact fderiv_comp_add_right (𝕜 := ℝ) (f := fun z => f (z, t + δ * (s - 1))) x
    rw [hfirst, fderiv_comp_add_right x, fderiv_fderiv_spatialSlice hf]
  have huheat : ∀ y ∈ Metric.ball 0 (r * 2), ∀ s ∈ Ioc (0 : ℝ) 1,
      HasDerivAt (fun q => u (y, q))
        (∑ i, ∑ j, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
          (b y (EuclideanSpace.basisFun (Fin n) ℝ j)) *
          fderiv ℝ (fderiv ℝ (fun z => u (z, s))) y
            (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)) s := by
    intro y hy s hs
    have hh := (hasDerivAt_timeSlice (hf.differentiable (by simp))
      (y + x) (t + δ * (s - 1))).scomp s
        ((((hasDerivAt_id s).sub_const 1).const_mul δ).const_add t)
    rw [hheat _ (hmem hy) _ (htime' hs)] at hh
    have hresult : HasDerivAt (fun q => u (y, q))
        (δ * Kernel.matrixLap (coefficientMatrix (a (y + x)))
          (spatialDerivative (spatialDerivative f) (y + x, t + δ * (s - 1)))) s := by
      simpa only [Function.comp_def, id_eq, mul_one, smul_eq_mul] using hh
    apply hresult.congr_deriv
    rw [hujet]
    simp only [b, smul_apply, real_inner_smul_right, Kernel.matrixLap,
        coefficientMatrix_apply, smul_eq_mul, Finset.mul_sum]
    simp only [mul_assoc]
  have he := hest b hbs hsymb hellb hholderb B hB u hu.contDiffOn huheat
    (fun y hy s hs => hb _ (hmem hy) _ (htime hs))
  rw [hujet] at he
  simp only [zero_add, sub_self, mul_zero, add_zero] at he
  have hx : x ∈ Metric.ball x (2 * r) := Metric.mem_ball_self (by positivity)
  have ht : t ∈ Ioo (t - δ) (t + δ) := by constructor <;> linarith
  rw [hheat x hx t ht, ← Real.norm_eq_abs, matrixLap_coefficientMatrix]
  apply (norm_principal_contraction_le (a x)
    (spatialDerivative (spatialDerivative f) (x, t))).trans
  have hnorm := norm_coefficient_le (a x) (hsym x hx) hlam
    (hlam.le.trans hlamΛ) (fun v => (hell x hx v).1) (fun v => (hell x hx v).2)
  calc
    (Fintype.card (Fin n) : ℝ) ^ 2 * ‖a x‖ *
        ‖spatialDerivative (spatialDerivative f) (x, t)‖ ≤
        (n : ℝ) ^ 2 * Λ * (C * B) := by
          simpa only [Fintype.card_fin] using
            mul_le_mul (mul_le_mul_of_nonneg_left hnorm (sq_nonneg (n : ℝ))) he
              (norm_nonneg (spatialDerivative (spatialDerivative f) (x, t)))
              (mul_nonneg (sq_nonneg (n : ℝ)) (hlam.le.trans hlamΛ))
    _ = ((n : ℝ) ^ 2 * Λ * C) * B := by ring



theorem exists_uniform_iterate_timeDerivative_bound
    (n : ℕ) (hn : 1 ≤ n) {lam Λ H : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H) (k : ℕ) :
    ∀ (r R α β a b : ℝ), 0 ≤ r → r < R → α < a → a ≤ b → b < β →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ContDiffOn ℝ ∞ A (Metric.ball 0 R) →
        (∀ x ∈ Metric.ball 0 R, ∀ v w,
          inner ℝ (A x v) w = inner ℝ v (A x w)) →
        (∀ x ∈ Metric.ball 0 R, ∀ v,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v) ∧
          inner ℝ v (A x v) ≤ Λ * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, ∀ y ∈ Metric.ball 0 R,
          ‖A x - A y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) →
        ∀ B : ℝ, 0 ≤ B →
        ∀ f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ, ContDiff ℝ ∞ f →
          (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β,
            timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
              (spatialDerivative (spatialDerivative f) (x, t))) →
          (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β, |f (x, t)| ≤ B) →
          ∀ x ∈ Metric.closedBall 0 r, ∀ t ∈ Icc a b,
            |((timeDerivative^[k]) f) (x, t)| ≤ C * B := by
  induction k with
  | zero =>
    intro r R α β a b hr hrR hα hab hβ
    refine ⟨1, by norm_num, ?_⟩
    intro A hA hsym hell hholder B hB f hf hheat hb x hx t ht
    simpa only [Function.iterate_zero_apply, one_mul] using
      hb x (lt_of_le_of_lt hx hrR) t ⟨hα.trans_le ht.1, ht.2.trans_lt hβ⟩
  | succ k ih =>
    intro r R α β a b hr hrR hα hab hβ
    let r' := (r + R) / 2
    let a' := (α + a) / 2
    let b' := (b + β) / 2
    let ρ := (R - r) / 4
    let δ := min ((a - α) / 4) ((β - b) / 4)
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδα : δ ≤ (a - α) / 4 := min_le_left _ _
    have hδβ : δ ≤ (β - b) / 4 := min_le_right _ _
    have hr' : 0 ≤ r' := by dsimp [r']; linarith
    have hr'R : r' < R := by dsimp [r']; linarith
    have hα' : α < a' := by dsimp [a']; linarith
    have hab' : a' ≤ b' := by dsimp [a', b']; linarith
    have hβ' : b' < β := by dsimp [b']; linarith
    obtain ⟨C₀, hC₀, hzero⟩ := ih r' R α β a' b' hr' hr'R hα' hab' hβ'
    obtain ⟨C₁, hC₁, hone⟩ := exists_uniform_static_heat_timeDerivative_bound
      n hn hρ hδ hlam hlamΛ hH
    refine ⟨C₁ * C₀, mul_pos hC₁ hC₀, ?_⟩
    intro A hA hsym hell hholder B hB f hf hheat hb x hx t ht
    obtain ⟨hfk, hheatk⟩ := iterate_timeDerivative_static_heat_equation hf isOpen_Ioo hheat k
    have hvaluek := hzero A hA hsym hell hholder B hB f hf hheat hb
    have hsmall {y : EuclideanSpace ℝ (Fin n)}
        (hy : y ∈ Metric.ball x (2 * ρ)) : y ∈ Metric.closedBall 0 r' := by
      have hdist := dist_triangle y x 0
      have hxy : dist y x < 2 * ρ := hy
      have hx' : dist x 0 ≤ r := hx
      change dist y 0 ≤ r'
      dsimp only [r', ρ] at *
      linarith
    have hlarge {y : EuclideanSpace ℝ (Fin n)}
        (hy : y ∈ Metric.ball x (2 * ρ)) : y ∈ Metric.ball 0 R :=
      lt_of_le_of_lt (hsmall hy) hr'R
    have hsmallt {s : ℝ} (hs : s ∈ Ioc (t - δ) t) : s ∈ Icc a' b' := by
      dsimp only [a', b']
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    have hlarget {s : ℝ} (hs : s ∈ Ioo (t - δ) (t + δ)) : s ∈ Ioo α β := by
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    have hbound := hone A x t (hA.mono (fun _ hy => hlarge hy))
      (fun y hy => hsym y (hlarge hy)) (fun y hy => hell y (hlarge hy))
      (fun y hy z hz => hholder y (hlarge hy) z (hlarge hz))
      (C₀ * B) (mul_nonneg hC₀.le hB) ((timeDerivative^[k]) f) hfk
      (fun y hy s hs => hheatk y (hlarge hy) s (hlarget hs))
      (fun y hy s hs => hvaluek y (hsmall hy) s (hsmallt hs))
    simpa only [Function.iterate_succ_apply', mul_assoc] using hbound




theorem exists_uniform_iterate_timeDerivative_bound_on
    (n : ℕ) (hn : 1 ≤ n) {lam Λ H : ℝ}
    (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) (hH : 0 ≤ H) (k : ℕ)
    (r R α β a b : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ContDiffOn ℝ ∞ A (Metric.ball 0 R) →
        (∀ x ∈ Metric.ball 0 R, ∀ v w,
          inner ℝ (A x v) w = inner ℝ v (A x w)) →
        (∀ x ∈ Metric.ball 0 R, ∀ v,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v) ∧
          inner ℝ v (A x v) ≤ Λ * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, ∀ y ∈ Metric.ball 0 R,
          ‖A x - A y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) →
        ∀ B : ℝ, 0 ≤ B →
        ∀ f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
          ContDiffOn ℝ ∞ f (Metric.ball 0 R ×ˢ Ioo α β) →
          (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β,
            timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
              (spatialDerivative (spatialDerivative f) (x, t))) →
          (∀ x ∈ Metric.ball 0 R, ∀ t ∈ Ioo α β, |f (x, t)| ≤ B) →
          ∀ x ∈ Metric.closedBall 0 r, ∀ t ∈ Icc a b,
            |((timeDerivative^[k]) f) (x, t)| ≤ C * B := by
  let R' := (r + R) / 2
  let α' := (α + a) / 2
  let β' := (b + β) / 2
  have hrR' : r < R' := by dsimp [R']; linarith
  have hR'R : R' < R := by dsimp [R']; linarith
  have hαα' : α < α' := by dsimp [α']; linarith
  have hα'a : α' < a := by dsimp [α']; linarith
  have hbβ' : b < β' := by dsimp [β']; linarith
  have hβ'β : β' < β := by dsimp [β']; linarith
  obtain ⟨C, hC, hest⟩ := exists_uniform_iterate_timeDerivative_bound
    n hn hlam hlamΛ hH k r R' α' β' a b hr hrR' hα'a hab hbβ'
  refine ⟨C, hC, ?_⟩
  intro A hA hsym hell hholder B hB f hf hheat hb
  let K : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
    Metric.closedBall 0 R' ×ˢ Icc α' β'
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKU : K ⊆ Metric.ball 0 R ×ˢ Ioo α β := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨lt_of_le_of_lt hx hR'R, hαα'.trans_le ht.1, ht.2.trans_lt hβ'β⟩
  obtain ⟨g, hg, _, hgf⟩ := exists_compact_smooth_extension hK
    (Metric.isOpen_ball.prod isOpen_Ioo) hKU hf
  have hsmall {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R') :
      x ∈ Metric.ball 0 R := lt_trans hx hR'R
  have hsmallt {t : ℝ} (ht : t ∈ Ioo α' β') : t ∈ Ioo α β :=
    ⟨hαα'.trans ht.1, ht.2.trans hβ'β⟩
  have hgheat : ∀ x ∈ Metric.ball 0 R', ∀ t ∈ Ioo α' β',
      timeDerivative g (x, t) = Kernel.matrixLap (coefficientMatrix (A x))
        (spatialDerivative (spatialDerivative g) (x, t)) := by
    intro x hx t ht
    have heq := hgf (x, t) ⟨Metric.ball_subset_closedBall hx, ht.1.le, ht.2.le⟩
    rw [(timeDerivative_eventuallyEq heq).eq_of_nhds,
      (spatialDerivative_eventuallyEq (spatialDerivative_eventuallyEq heq)).eq_of_nhds]
    exact hheat x (hsmall hx) t (hsmallt ht)
  have hgb : ∀ x ∈ Metric.ball 0 R', ∀ t ∈ Ioo α' β', |g (x, t)| ≤ B := by
    intro x hx t ht
    rw [(hgf (x, t) ⟨Metric.ball_subset_closedBall hx, ht.1.le, ht.2.le⟩).eq_of_nhds]
    exact hb x (hsmall hx) t (hsmallt ht)
  have hbound := hest A (hA.mono (fun _ hx => hsmall hx))
    (fun x hx => hsym x (hsmall hx)) (fun x hx => hell x (hsmall hx))
    (fun x hx y hy => hholder x (hsmall hx) y (hsmall hy)) B hB g hg hgheat hgb
  intro x hx t ht
  have hp : (x, t) ∈ K :=
    ⟨hx.trans hrR'.le, hα'a.le.trans ht.1, ht.2.trans hbβ'.le⟩
  rw [← (iterate_timeDerivative_eventuallyEq (hgf (x, t) hp) k).eq_of_nhds]
  exact hbound x hx t ht

end Poincare.Parabolic.Interior
