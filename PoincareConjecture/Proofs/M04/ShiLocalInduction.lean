import PoincareConjecture.Proofs.M04.ShiShiftedHeat
import PoincareConjecture.Proofs.M04.ShiCutoffConsumer









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def shiPhysicalCutoffSupports
    (g : ℝ → RiemannianMetric n M) (D : (t : ℝ) → LeviCivitaData (g t))
    (T : ℝ) (C : Set M) (η : ℝ → M → ℝ) (L G : ℝ) : Prop :=
  ∀ t ∈ Ioc 0 T, ∀ x ∈ interior C, 0 < η t x →
    ∀ ε > 0, ∃ e : ℝ → M → ℝ, ∃ ed : ℝ, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (e t) U ∧
      e t x = η t x ∧ (∀ᶠ y in 𝓝 x, e t y ≤ η t y) ∧
      (∀ᶠ s in 𝓝[ Icc 0 t ] t, e s x ≤ η s x) ∧
      HasDerivWithinAt (fun s => e s x) ed (Icc 0 t) t ∧
      scalarGradientSq (g t) (e t) x ≤ G * η t x ∧
      ed - (D t).laplacian (e t) x ≤ L + ε

private theorem cutoffThreshold_nonneg (c d L G Θ : ℝ) :
    0 ≤ shiCutoffThreshold c d L G Θ := by
  unfold shiCutoffThreshold
  exact (show (0 : ℝ) ≤ 1 by norm_num).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem shi_cutoff_half_window_bound
    (g : ℝ → RiemannianMetric n M) (D : (t : ℝ) → LeviCivitaData (g t))
    {C : Set M} (hC : IsCompact C) {T θ Θ c d L G : ℝ}
    (hθ : 0 < θ) (hθT : θ ≤ T) (hθΘ : θ ≤ Θ)
    (hc : 0 < c) (hd : 0 ≤ d) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (Q η : ℝ → M → ℝ)
    (hQ : ContinuousOn (Function.uncurry Q) (Icc 0 T ×ˢ C))
    (hη : ContinuousOn (Function.uncurry η) (Icc 0 T ×ˢ C))
    (hQ0 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ Q t x)
    (hη0 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ η t x)
    (hη1 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, η t x ≤ 1)
    (hboundary : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, η t x = 0)
    (hspace : ∀ t ∈ Ioc 0 T, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (Q t))
    (htime : ∀ t ∈ Ioc 0 T, ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => Q s x) (Icc 0 T) t)
    (hheat : ∀ t ∈ Icc (θ / 2) θ, ∀ x ∈ interior C,
      θ * (derivWithin (fun s => Q s x) (Icc 0 T) t -
        (D t).laplacian (Q t) x) ≤ -c * Q t x ^ 2 + d)
    (hsupport : shiPhysicalCutoffSupports g D T C η L G)
    {x : M} (hx : x ∈ C) (hxη : η θ x = 1) :
    Q θ x ≤ 2 * shiCutoffThreshold c d (Θ * L) (Θ * G) (1 / 2) := by
  let φ : ℝ → ℝ := fun s => θ / 2 + θ * s
  have hφc : Continuous φ := continuous_const.add (continuous_const.mul continuous_id)
  have hφd (s : ℝ) : HasDerivAt φ θ s := by
    change HasDerivAt (fun r : ℝ => θ / 2 + θ * r) θ s
    simpa only [id, mul_one] using
      (((hasDerivAt_id s).const_mul θ).const_add (θ / 2))
  have hφwin {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
      φ s ∈ Icc (θ / 2) θ := by
    dsimp only [φ]
    constructor
    · nlinarith only [mul_nonneg hθ.le hs.1]
    · nlinarith only [mul_le_mul_of_nonneg_left hs.2 hθ.le]
  have hφT : MapsTo φ (Icc (0 : ℝ) (1 / 2)) (Icc 0 T) := by
    intro s hs
    exact ⟨(half_pos hθ).le.trans (hφwin hs).1, (hφwin hs).2.trans hθT⟩
  have hφpos {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 2)) : φ s ∈ Ioc 0 T :=
    ⟨(half_pos hθ).trans_le (hφwin ⟨hs.1.le, hs.2⟩).1,
      (hφT ⟨hs.1.le, hs.2⟩).2⟩
  have hφpast (s : ℝ) : MapsTo φ (Icc 0 s) (Icc 0 (φ s)) := by
    intro r hr
    dsimp only [φ]
    constructor
    · nlinarith only [hθ, mul_nonneg hθ.le hr.1]
    · nlinarith only [mul_le_mul_of_nonneg_left hr.2 hθ.le]
  have hmap : Continuous (fun p : ℝ × M => (φ p.1, p.2)) :=
    (hφc.comp continuous_fst).prodMk continuous_snd
  have hmapC : MapsTo (fun p : ℝ × M => (φ p.1, p.2))
      (Icc (0 : ℝ) (1 / 2) ×ˢ C) (Icc 0 T ×ˢ C) :=
    fun p hp => ⟨hφT hp.1, hp.2⟩
  have hQ' : ContinuousOn (Function.uncurry (fun s y => Q (φ s) y))
      (Icc (0 : ℝ) (1 / 2) ×ˢ C) := hQ.comp hmap.continuousOn hmapC
  have hη' : ContinuousOn (Function.uncurry (fun s y => η (φ s) y))
      (Icc (0 : ℝ) (1 / 2) ×ˢ C) := hη.comp hmap.continuousOn hmapC
  have hheat' : ∀ s ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ interior C, ∃ qd : ℝ,
      HasDerivWithinAt (fun r => Q (φ r) y) qd (Icc 0 s) s ∧
        qd - θ * (D (φ s)).laplacian (Q (φ s)) y ≤ -c * Q (φ s) y ^ 2 + d := by
    intro s hs y hy
    let qd := derivWithin (fun r => Q r y) (Icc 0 T) (φ s)
    refine ⟨qd * θ, ?_, ?_⟩
    · exact (htime (φ s) (hφpos hs) y).hasDerivWithinAt.comp s
        (hφd s).hasDerivWithinAt (fun r hr => hφT ⟨hr.1, hr.2.trans hs.2⟩)
    · have hh := hheat (φ s) (hφwin ⟨hs.1.le, hs.2⟩) y hy
      dsimp only [qd]
      nlinarith only [hh]
  have hsupport' : ∀ s ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ interior C,
      0 < η (φ s) y → ∀ ε > 0,
      ∃ e : ℝ → M → ℝ, ∃ ed : ℝ, ∃ U : Set M,
        IsOpen U ∧ y ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (e s) U ∧
        e s y = η (φ s) y ∧ (∀ᶠ z in 𝓝 y, e s z ≤ η (φ s) z) ∧
        (∀ᶠ r in 𝓝[ Icc 0 s ] s, e r y ≤ η (φ r) y) ∧
        HasDerivWithinAt (fun r => e r y) ed (Icc 0 s) s ∧
        θ * scalarGradientSq (g (φ s)) (e s) y ≤ (Θ * G) * η (φ s) y ∧
        ed - θ * (D (φ s)).laplacian (e s) y ≤ Θ * L + ε := by
    intro s hs y hy hyη ε hε
    obtain ⟨e, ed, U, hU, hyU, he, heq, heSpace, heTime, hed, heGrad, heHeat⟩ :=
      hsupport (φ s) (hφpos hs) y hy hyη (ε / θ) (div_pos hε hθ)
    refine ⟨fun r z => e (φ r) z, ed * θ, U, hU, hyU, he, heq, heSpace, ?_, ?_, ?_, ?_⟩
    · exact (hφc.continuousAt.continuousWithinAt.tendsto_nhdsWithin
        (hφpast s)).eventually heTime
    · exact hed.comp s (hφd s).hasDerivWithinAt (hφpast s)
    · have hscaled := mul_le_mul_of_nonneg_left heGrad hθ.le
      have hcap := mul_le_mul_of_nonneg_right hθΘ (mul_nonneg hG hyη.le)
      nlinarith only [hscaled, hcap]
    · have hscaled := mul_le_mul_of_nonneg_left heHeat hθ.le
      have hcap := mul_le_mul_of_nonneg_right hθΘ hL
      have herr : θ * (ε / θ) = ε := by field_simp [ne_of_gt hθ]
      nlinarith only [hscaled, hcap, herr]
  have hΘ : 0 ≤ Θ := hθ.le.trans hθΘ
  have hb := shi_cutoff_bound (fun s => g (φ s)) (fun s => D (φ s)) hC
    (S := 1 / 2) (κ := θ) (c := c) (d := d) (L := Θ * L) (G := Θ * G)
    (Θ := 1 / 2) (a := 0) (I := 0)
    (by norm_num) hθ.le hc hd (mul_nonneg hΘ hL) (mul_nonneg hΘ hG)
    (by norm_num) (by norm_num) (by norm_num)
    (fun s y => Q (φ s) y) (fun s y => η (φ s) y) hQ' hη'
    (fun s hs y hy => hQ0 (φ s) (hφT hs) y hy)
    (fun s hs y hy => hη0 (φ s) (hφT hs) y hy)
    (fun s hs y hy => hη1 (φ s) (hφT hs) y hy)
    (fun s hs y hy => hboundary (φ s) (hφT hs) y hy)
    (by intro y hy; simp)
    (fun s hs => hspace (φ s) (hφpos hs)) hheat' hsupport'
  have hfinal := hb (1 / 2) ⟨by norm_num, le_rfl⟩ x hx
  have hφend : φ (1 / 2) = θ := by dsimp [φ]; ring
  rw [hφend, hxη, zero_add, mul_one,
    max_eq_right (cutoffThreshold_nonneg c d (Θ * L) (Θ * G) (1 / 2))] at hfinal
  linarith only [hfinal]

noncomputable def shiLocalBernsteinCoefficient (H : ℝ) : ℝ :=
  1 / (2 * (9 * H ^ 2 + 1) ^ 2)

noncomputable def shiLocalBernsteinRemainder (n m : ℕ) (Λ H : ℝ) : ℝ :=
  (Λ * shiEnergyReactionCoefficient n m * H ^ 3 +
    (Λ * shiEnergyReactionCoefficient n (m + 1) * H + 1) * (9 * H ^ 2 + 1)) ^ 2 / 2 +
    (Λ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4 * (9 * H ^ 2 + 1)

noncomputable def shiLocalBernsteinEnergy {g : RiemannianMetric n M}
    (l m : ℕ) (ρ H : ℝ) (D : LeviCivitaData g) (x : M) : ℝ :=
  (8 * H ^ 2 + 1 + shiShiftedEnergy l ρ D m x) * shiShiftedEnergy l ρ D (m + 1) x

private theorem local_coefficient_pos (H : ℝ) : 0 < shiLocalBernsteinCoefficient H := by
  unfold shiLocalBernsteinCoefficient
  positivity

private theorem local_remainder_nonneg (n m : ℕ) (Λ H : ℝ) :
    0 ≤ shiLocalBernsteinRemainder n m Λ H := by
  unfold shiLocalBernsteinRemainder
  positivity

private theorem local_energy_nonneg {g : RiemannianMetric n M}
    (l m : ℕ) (ρ H : ℝ) (D : LeviCivitaData g) (x : M) :
    0 ≤ shiLocalBernsteinEnergy l m ρ H D x := by
  unfold shiLocalBernsteinEnergy shiShiftedEnergy
  positivity

private theorem local_energy_ge_target {g : RiemannianMetric n M}
    (l m : ℕ) (ρ H : ℝ) (D : LeviCivitaData g) (x : M) :
    (ρ ^ (m + 1 - l) * D.curvatureDerivativeNorm (m + 1) x) ^ 2 ≤
      shiLocalBernsteinEnergy l m ρ H D x := by
  have hW : 0 ≤ shiShiftedEnergy l ρ D (m + 1) x := by
    unfold shiShiftedEnergy
    positivity
  have hA : 1 ≤ 8 * H ^ 2 + 1 + shiShiftedEnergy l ρ D m x := by
    have hm : 0 ≤ shiShiftedEnergy l ρ D m x := by
      unfold shiShiftedEnergy
      positivity
    nlinarith only [sq_nonneg H, hm]
  simpa only [shiLocalBernsteinEnergy, shiShiftedEnergy, mul_pow, one_mul] using
    mul_le_mul_of_nonneg_right hA hW

private theorem local_energy_smooth {g : RiemannianMetric n M}
    (l m : ℕ) (ρ H : ℝ) (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (shiLocalBernsteinEnergy l m ρ H D) := by
  have hE (j : ℕ) :
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (D.curvatureDerivativeNorm j y) ^ 2) := by
    apply contMDiff_tensorNorm_sq
    induction j with
    | zero => exact isSmoothCovariantTensor_riemannEvaluation D
    | succ j ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih
  have hW (j : ℕ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (shiShiftedEnergy l ρ D j) :=
    contMDiff_const.mul (hE j)
  exact (contMDiff_const.add (hW m)).mul (hW (m + 1))

private theorem local_energy_continuous {T : ℝ} (F : RicciFlow n M (Icc 0 T))
    (l m : ℕ) (ρ H : ℝ) (C : Set M) :
    ContinuousOn (Function.uncurry (fun t => shiLocalBernsteinEnergy l m ρ H (F.connection t)))
      (Icc 0 T ×ˢ C) := by
  have hW (j : ℕ) : ContinuousOn
      (fun p : ℝ × M => shiShiftedEnergy l ρ (F.connection p.1) j p.2)
      (Icc 0 T ×ˢ C) := by
    exact continuousOn_const.mul
      ((contMDiffOn_flow_curvatureDerivativeEnergy F j).continuousOn.mono
        (fun p hp => ⟨hp.1, mem_univ p.2⟩))
  exact (continuousOn_const.add (hW m)).mul (hW (m + 1))

private theorem local_energy_differentiable {T : ℝ} (F : RicciFlow n M (Icc 0 T))
    (l m : ℕ) (ρ H : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    DifferentiableWithinAt ℝ
      (fun s => shiLocalBernsteinEnergy l m ρ H (F.connection s) x) (Icc 0 T) t := by
  have hW (j : ℕ) : DifferentiableWithinAt ℝ
      (fun s => shiShiftedEnergy l ρ (F.connection s) j x) (Icc 0 T) t := by
    have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) := contMDiff_id.prodMk contMDiff_const
    have hE : ContDiffOn ℝ ∞
        (fun s => ((F.connection s).curvatureDerivativeNorm j x) ^ 2) (Icc 0 T) :=
      (contMDiffOn_flow_curvatureDerivativeEnergy F j).comp
        hslice.contMDiffOn (fun s hs => ⟨hs, mem_univ x⟩) |>.contDiffOn
    exact (hE.differentiableOn (by simp) t ht).const_mul ((ρ ^ (j - l)) ^ 2)
  exact ((hW m).const_add (8 * H ^ 2 + 1)).mul (hW (m + 1))

private theorem local_energy_heat {T : ℝ} (F : RicciFlow n M (Icc 0 T))
    {l m : ℕ} (hlm : l ≤ m) {ρ Θ H : ℝ}
    (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hH : 0 ≤ H)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M)
    (hbound : ∀ j ≤ m, ρ ^ (j - l) * (F.connection t).curvatureDerivativeNorm j x ≤ H) :
    ρ ^ 2 * (derivWithin (fun s => shiLocalBernsteinEnergy l m ρ H (F.connection s) x)
      (Icc 0 T) t - (F.connection t).laplacian
        (shiLocalBernsteinEnergy l m ρ H (F.connection t)) x) ≤
      -shiLocalBernsteinCoefficient H *
        (shiLocalBernsteinEnergy l m ρ H (F.connection t) x) ^ 2 +
        shiLocalBernsteinRemainder n m (shiShiftedReactionScale l Θ) H := by
  have hh := shi_shifted_bernstein_heat_inequality F hlm hρ hρΘ hH ht x hbound
  dsimp only at hh
  dsimp only [shiLocalBernsteinEnergy, shiLocalBernsteinCoefficient,
    shiLocalBernsteinRemainder] at hh ⊢
  have hQeq (s : ℝ) :
      shiLocalBernsteinEnergy l m ρ H (F.connection s) =
        (fun y =>
          (8 * H ^ 2 + 1 +
              shiShiftedEnergy l ρ (F.connection s) m y) *
            shiShiftedEnergy l ρ (F.connection s) (m + 1) y) := rfl
  rw [hQeq t]
  convert hh using 1 <;> ring

theorem shi_shifted_local_step
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) {C : Set M} (hC : IsCompact C)
    {l m : ℕ} (hlm : l ≤ m) {θ Θ H L G : ℝ}
    (hθ : 0 < θ) (hθT : θ ≤ T) (hθΘ : θ ≤ Θ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hG : 0 ≤ G) (η : ℝ → M → ℝ)
    (hη : ContinuousOn (Function.uncurry η) (Icc 0 T ×ˢ C))
    (hη0 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ η t x)
    (hη1 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, η t x ≤ 1)
    (hboundary : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, η t x = 0)
    (hsupport : shiPhysicalCutoffSupports F.metric F.connection T C η L G)
    (hbound : ∀ j ≤ m, ∀ t ∈ Icc (θ / 2) θ, ∀ x ∈ C,
      (Real.sqrt θ) ^ (j - l) * (F.connection t).curvatureDerivativeNorm j x ≤ H)
    {x : M} (hx : x ∈ C) (hxη : η θ x = 1) :
    let U := shiCutoffThreshold (shiLocalBernsteinCoefficient H)
      (shiLocalBernsteinRemainder n m (shiShiftedReactionScale l Θ) H)
      (Θ * L) (Θ * G) (1 / 2)
    (F.connection θ).curvatureDerivativeNorm (m + 1) x ≤
      (1 + Real.sqrt (2 * U)) / θ ^ (((m + 1 - l : ℕ) : ℝ) / 2) := by
  let U := shiCutoffThreshold (shiLocalBernsteinCoefficient H)
    (shiLocalBernsteinRemainder n m (shiShiftedReactionScale l Θ) H)
    (Θ * L) (Θ * G) (1 / 2)
  let Q : ℝ → M → ℝ :=
    fun s => shiLocalBernsteinEnergy l m (Real.sqrt θ) H (F.connection s)
  have hρ : 0 ≤ Real.sqrt θ := Real.sqrt_nonneg θ
  have hρsq : (Real.sqrt θ) ^ 2 = θ := Real.sq_sqrt hθ.le
  have hρΘ : (Real.sqrt θ) ^ 2 ≤ Θ := by
    rw [hρsq]
    exact hθΘ
  have hheat : ∀ s ∈ Icc (θ / 2) θ, ∀ y ∈ interior C,
      θ * (derivWithin (fun r => Q r y) (Icc 0 T) s -
        (F.connection s).laplacian (Q s) y) ≤
      -shiLocalBernsteinCoefficient H * Q s y ^ 2 +
        shiLocalBernsteinRemainder n m (shiShiftedReactionScale l Θ) H := by
    intro s hs y hy
    have hsT : s ∈ Ioc 0 T :=
      ⟨(half_pos hθ).trans_le hs.1, hs.2.trans hθT⟩
    simpa only [hρsq] using local_energy_heat F hlm hρ hρΘ hH hsT y
      (fun j hj => hbound j hj s hs y (interior_subset hy))
  have hQbound : Q θ x ≤ 2 * U :=
    shi_cutoff_half_window_bound F.metric F.connection hC hθ hθT hθΘ
      (local_coefficient_pos H) (local_remainder_nonneg n m _ H) hL hG Q η
      (local_energy_continuous F l m (Real.sqrt θ) H C) hη
      (fun s hs y hy => local_energy_nonneg l m (Real.sqrt θ) H (F.connection s) y)
      hη0 hη1 hboundary
      (fun s hs => local_energy_smooth l m (Real.sqrt θ) H (F.connection s))
      (fun s hs y => local_energy_differentiable F l m (Real.sqrt θ) H
        ⟨hs.1.le, hs.2⟩ y)
      hheat hsupport hx hxη
  have hnorm := Real.le_sqrt_of_sq_le
    ((local_energy_ge_target l m (Real.sqrt θ) H (F.connection θ) x).trans hQbound)
  have hpowpos : 0 < (Real.sqrt θ) ^ (m + 1 - l) :=
    pow_pos (Real.sqrt_pos.2 hθ) _
  have hrpow : θ ^ (((m + 1 - l : ℕ) : ℝ) / 2) =
      (Real.sqrt θ) ^ (m + 1 - l) := by
    rw [Real.rpow_div_two_eq_sqrt _ hθ.le, Real.rpow_natCast]
  change (F.connection θ).curvatureDerivativeNorm (m + 1) x ≤
    (1 + Real.sqrt (2 * U)) / θ ^ (((m + 1 - l : ℕ) : ℝ) / 2)
  rw [hrpow]
  apply (le_div_iff₀ hpowpos).2
  calc
    _ = (Real.sqrt θ) ^ (m + 1 - l) *
        (F.connection θ).curvatureDerivativeNorm (m + 1) x := mul_comm _ _
    _ ≤ Real.sqrt (2 * U) := hnorm
    _ ≤ 1 + Real.sqrt (2 * U) := by linarith

theorem shi_initial_local_step
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) {C : Set M} (hC : IsCompact C)
    (m : ℕ) {Θ H K L G : ℝ} (hT : 0 < T) (hTΘ : T ≤ Θ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (η : ℝ → M → ℝ)
    (hη : ContinuousOn (Function.uncurry η) (Icc 0 T ×ˢ C))
    (hη0 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, 0 ≤ η t x)
    (hη1 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, η t x ≤ 1)
    (hboundary : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, η t x = 0)
    (hsupport : shiPhysicalCutoffSupports F.metric F.connection T C η L G)
    (hbound : ∀ j ≤ m, ∀ t ∈ Icc 0 T, ∀ x ∈ C,
      (F.connection t).curvatureDerivativeNorm j x ≤ H)
    (hinitial : ∀ x ∈ C, (F.connection 0).curvatureDerivativeNorm (m + 1) x ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) {x : M} (hx : x ∈ C) (hxη : η t x = 1) :
    let U := max ((9 * H ^ 2 + 1) * K ^ 2)
      (shiCutoffThreshold (shiLocalBernsteinCoefficient H)
        (shiLocalBernsteinRemainder n m (max 1 Θ) H) L G (1 + Θ))
    (F.connection t).curvatureDerivativeNorm (m + 1) x ≤ 1 + Real.sqrt U := by
  let Q : ℝ → M → ℝ := fun s => shiLocalBernsteinEnergy 0 m 1 H (F.connection s)
  let U := max ((9 * H ^ 2 + 1) * K ^ 2)
    (shiCutoffThreshold (shiLocalBernsteinCoefficient H)
      (shiLocalBernsteinRemainder n m (max 1 Θ) H) L G (1 + Θ))
  have hQ0 (s : ℝ) (y : M) : 0 ≤ Q s y :=
    local_energy_nonneg 0 m 1 H (F.connection s) y
  have hinit : ∀ y ∈ C, 1 * η 0 y * Q 0 y ≤ (9 * H ^ 2 + 1) * K ^ 2 := by
    intro y hy
    have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    have hNm : 0 ≤ (F.connection 0).curvatureDerivativeNorm m y := Real.sqrt_nonneg _
    have hNk : 0 ≤ (F.connection 0).curvatureDerivativeNorm (m + 1) y := Real.sqrt_nonneg _
    have hm : ((F.connection 0).curvatureDerivativeNorm m y) ^ 2 ≤ H ^ 2 :=
      (sq_le_sq₀ hNm hH).2 (hbound m le_rfl 0 h0T y hy)
    have hk : ((F.connection 0).curvatureDerivativeNorm (m + 1) y) ^ 2 ≤ K ^ 2 :=
      (sq_le_sq₀ hNk hK).2 (hinitial y hy)
    have hQ : Q 0 y ≤ (9 * H ^ 2 + 1) * K ^ 2 := by
      have hA : 8 * H ^ 2 + 1 + ((F.connection 0).curvatureDerivativeNorm m y) ^ 2 ≤
          9 * H ^ 2 + 1 := by linarith only [hm]
      simpa only [Q, shiLocalBernsteinEnergy, shiShiftedEnergy, one_pow, one_mul] using
        mul_le_mul hA hk (sq_nonneg _) (by positivity : 0 ≤ 9 * H ^ 2 + 1)
    calc
      1 * η 0 y * Q 0 y ≤ Q 0 y := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hη1 0 h0T y hy) (hQ0 0 y)
      _ ≤ (9 * H ^ 2 + 1) * K ^ 2 := hQ
  have hheat : ∀ s ∈ Ioc 0 T, ∀ y ∈ interior C, ∃ qd : ℝ,
      HasDerivWithinAt (fun r => Q r y) qd (Icc 0 s) s ∧
        qd - 1 * (F.connection s).laplacian (Q s) y ≤
          -shiLocalBernsteinCoefficient H * Q s y ^ 2 +
            shiLocalBernsteinRemainder n m (max 1 Θ) H := by
    intro s hs y hy
    refine ⟨derivWithin (fun r => Q r y) (Icc 0 T) s, ?_, ?_⟩
    · exact (local_energy_differentiable F 0 m 1 H ⟨hs.1.le, hs.2⟩ y).hasDerivWithinAt.mono
        (fun r hr => ⟨hr.1, hr.2.trans hs.2⟩)
    · have hρΘ : (1 : ℝ) ^ 2 ≤ max 1 Θ := by simpa using le_max_left (1 : ℝ) Θ
      have hh := local_energy_heat F (Nat.zero_le m) (by norm_num : (0 : ℝ) ≤ 1)
        hρΘ hH hs y (fun j hj => by
          simpa only [one_pow, one_mul] using hbound j hj s ⟨hs.1.le, hs.2⟩ y
            (interior_subset hy))
      simpa only [one_pow, one_mul, shiShiftedReactionScale, pow_zero, mul_one] using hh
  have hsupport' : ∀ s ∈ Ioc 0 T, ∀ y ∈ interior C, 0 < η s y →
      ∀ ε > 0, ∃ e : ℝ → M → ℝ, ∃ ed : ℝ, ∃ V : Set M,
        IsOpen V ∧ y ∈ V ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (e s) V ∧
        e s y = η s y ∧ (∀ᶠ z in 𝓝 y, e s z ≤ η s z) ∧
        (∀ᶠ r in 𝓝[ Icc 0 s ] s, e r y ≤ η r y) ∧
        HasDerivWithinAt (fun r => e r y) ed (Icc 0 s) s ∧
        1 * scalarGradientSq (F.metric s) (e s) y ≤ G * η s y ∧
        ed - 1 * (F.connection s).laplacian (e s) y ≤ L + ε := by
    simpa only [shiPhysicalCutoffSupports, one_mul] using hsupport
  have hb := shi_cutoff_bound F.metric F.connection hC
    (S := T) (κ := 1) (c := shiLocalBernsteinCoefficient H)
    (d := shiLocalBernsteinRemainder n m (max 1 Θ) H) (L := L) (G := G)
    (Θ := 1 + Θ) (a := 1) (I := (9 * H ^ 2 + 1) * K ^ 2)
    hT (by norm_num) (local_coefficient_pos H) (local_remainder_nonneg n m _ H)
    hL hG (by norm_num) (by positivity) (by linarith only [hTΘ]) Q η
    (local_energy_continuous F 0 m 1 H C) hη (fun s hs y hy => hQ0 s y)
    hη0 hη1 hboundary hinit
    (fun s hs => local_energy_smooth 0 m 1 H (F.connection s)) hheat hsupport'
  have hweighted : (1 + t) * Q t x ≤ U := by
    simpa only [hxη, mul_one] using hb t ht x hx
  have hQbound : Q t x ≤ U := by
    have hweight : 1 ≤ 1 + t := by linarith only [ht.1]
    have hweightQ : Q t x ≤ (1 + t) * Q t x := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hweight (hQ0 t x)
    exact hweightQ.trans hweighted
  have hsquare : ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2 ≤ U := by
    simpa only [one_pow, one_mul] using
      (local_energy_ge_target 0 m 1 H (F.connection t) x).trans hQbound
  have hnorm := Real.le_sqrt_of_sq_le hsquare
  change (F.connection t).curvatureDerivativeNorm (m + 1) x ≤ 1 + Real.sqrt U
  linarith only [hnorm]

end PoincareConjecture.M04
