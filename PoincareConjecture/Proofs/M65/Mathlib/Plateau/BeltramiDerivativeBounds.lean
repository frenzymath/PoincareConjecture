import PoincareConjecture.Proofs.M65.Mathlib.Plateau.SmoothBeurling

set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter LineDeriv
open scoped Topology SchwartzMap ContDiff ComplexConjugate LineDeriv

namespace Complex

def planeDerivativeL2Budget : ℕ → 𝓢(ℂ, ℂ) → ℝ
  | 0, h => ‖h.toLp 2 volume‖
  | m + 1, h => planeDerivativeL2Budget m h +
      planeDerivativeL2Budget m (∂_{(1 : ℂ)} h) +
      planeDerivativeL2Budget m (∂_{I} h)

private theorem budget_nonneg (m : ℕ) (h : 𝓢(ℂ, ℂ)) :
    0 ≤ planeDerivativeL2Budget m h := by
  induction m generalizing h with
  | zero => exact norm_nonneg _
  | succ m ih => exact add_nonneg (add_nonneg (ih _) (ih _)) (ih _)

private theorem budget_le_succ (m : ℕ) (h : 𝓢(ℂ, ℂ)) :
    planeDerivativeL2Budget m h ≤ planeDerivativeL2Budget (m + 1) h := by
  dsimp only [planeDerivativeL2Budget]
  linarith [budget_nonneg m (∂_{(1 : ℂ)} h), budget_nonneg m (∂_{I} h)]

theorem planeDerivativeL2Budget_mono {m n : ℕ} (hmn : m ≤ n) (h : 𝓢(ℂ, ℂ)) :
    planeDerivativeL2Budget m h ≤ planeDerivativeL2Budget n h :=
  (monotone_nat_of_le_succ fun j => budget_le_succ j h) hmn

theorem planeDerivativeL2Budget_coordinate_le (m : ℕ) (h : 𝓢(ℂ, ℂ)) (i : Fin 2) :
    planeDerivativeL2Budget m (∂_{orthonormalBasisOneI i} h) ≤
      planeDerivativeL2Budget (m + 1) h := by
  rw [coe_orthonormalBasisOneI]
  fin_cases i
  · change planeDerivativeL2Budget m (∂_{(1 : ℂ)} h) ≤ _
    change _ ≤ planeDerivativeL2Budget m h + planeDerivativeL2Budget m (∂_{(1 : ℂ)} h) +
      planeDerivativeL2Budget m (∂_{I} h)
    linarith [budget_nonneg m h, budget_nonneg m (∂_{I} h)]
  · change planeDerivativeL2Budget m (∂_{I} h) ≤ _
    change _ ≤ planeDerivativeL2Budget m h + planeDerivativeL2Budget m (∂_{(1 : ℂ)} h) +
      planeDerivativeL2Budget m (∂_{I} h)
    linarith [budget_nonneg m h, budget_nonneg m (∂_{(1 : ℂ)} h)]

private theorem budget_add_le (m : ℕ) (f g : 𝓢(ℂ, ℂ)) :
    planeDerivativeL2Budget m (f + g) ≤
      planeDerivativeL2Budget m f + planeDerivativeL2Budget m g := by
  induction m generalizing f g with
  | zero =>
      change ‖(SchwartzMap.toLpCLM ℂ ℂ 2 volume) (f + g)‖ ≤ _
      rw [map_add]
      exact norm_add_le _ _
  | succ m ih =>
      simp only [planeDerivativeL2Budget, lineDerivOp_add]
      linarith [ih f g, ih (∂_{(1 : ℂ)} f) (∂_{(1 : ℂ)} g),
        ih (∂_{I} f) (∂_{I} g)]

private theorem localized_budget_succ_le (m : ℕ) (μ h : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ))
    (hμ1 : HasCompactSupport ((∂_{(1 : ℂ)} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ))
    (hμI : HasCompactSupport ((∂_{I} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ)) :
    planeDerivativeL2Budget (m + 1) (localizedBeurling μ hμ h) ≤
      planeDerivativeL2Budget m (localizedBeurling μ hμ h) +
      (planeDerivativeL2Budget m (localizedBeurling μ hμ (∂_{(1 : ℂ)} h)) +
        planeDerivativeL2Budget m (localizedBeurling (∂_{(1 : ℂ)} μ) hμ1 h)) +
      (planeDerivativeL2Budget m (localizedBeurling μ hμ (∂_{I} h)) +
        planeDerivativeL2Budget m (localizedBeurling (∂_{I} μ) hμI h)) := by
  simp only [planeDerivativeL2Budget, lineDeriv_localizedBeurling]
  exact _root_.add_le_add (_root_.add_le_add le_rfl (budget_add_le m _ _))
    (budget_add_le m _ _)

private theorem exists_localized_budget_bound (m : ℕ) (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : 𝓢(ℂ, ℂ),
      planeDerivativeL2Budget m (localizedBeurling μ hμ h) ≤
        C * planeDerivativeL2Budget m h := by
  induction m generalizing μ with
  | zero =>
      refine ⟨SchwartzMap.seminorm ℝ 0 0 μ, apply_nonneg _ _, fun h => ?_⟩
      exact norm_localizedBeurling_toLp_le μ hμ (μ.norm_le_seminorm ℝ) h
  | succ m ih =>
      have hμ1 : HasCompactSupport ((∂_{(1 : ℂ)} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
        hμ.fderiv_apply (𝕜 := ℝ) 1
      have hμI : HasCompactSupport ((∂_{I} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
        hμ.fderiv_apply (𝕜 := ℝ) I
      obtain ⟨C, hC, hbound⟩ := ih μ hμ
      obtain ⟨C1, hC1, hbound1⟩ := ih (∂_{(1 : ℂ)} μ) hμ1
      obtain ⟨CI, hCI, hboundI⟩ := ih (∂_{I} μ) hμI
      refine ⟨C + C1 + CI, by positivity, fun h => ?_⟩
      have hproduct := localized_budget_succ_le m μ h hμ hμ1 hμI
      have hlow := budget_le_succ m h
      have hhigh : planeDerivativeL2Budget (m + 1) h =
          planeDerivativeL2Budget m h + planeDerivativeL2Budget m (∂_{(1 : ℂ)} h) +
            planeDerivativeL2Budget m (∂_{I} h) := rfl
      nlinarith [hbound h, hbound (∂_{(1 : ℂ)} h), hbound (∂_{I} h),
        hbound1 h, hboundI h]

theorem exists_localized_principal_budget_bound (m : ℕ) (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : 𝓢(ℂ, ℂ),
      planeDerivativeL2Budget (m + 1) (localizedBeurling μ hμ h) ≤
        k * planeDerivativeL2Budget (m + 1) h + C * planeDerivativeL2Budget m h := by
  have hμ1 : HasCompactSupport ((∂_{(1 : ℂ)} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
    hμ.fderiv_apply (𝕜 := ℝ) 1
  have hμI : HasCompactSupport ((∂_{I} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
    hμ.fderiv_apply (𝕜 := ℝ) I
  induction m with
  | zero =>
      obtain ⟨C1, hC1, hbound1⟩ := exists_localized_budget_bound 0 (∂_{(1 : ℂ)} μ) hμ1
      obtain ⟨CI, hCI, hboundI⟩ := exists_localized_budget_bound 0 (∂_{I} μ) hμI
      refine ⟨C1 + CI, add_nonneg hC1 hCI, fun h => ?_⟩
      have hproduct := localized_budget_succ_le 0 μ h hμ hμ1 hμI
      have hhigh : planeDerivativeL2Budget 1 h =
          planeDerivativeL2Budget 0 h + planeDerivativeL2Budget 0 (∂_{(1 : ℂ)} h) +
            planeDerivativeL2Budget 0 (∂_{I} h) := rfl
      have hprincipal (f : 𝓢(ℂ, ℂ)) :
          planeDerivativeL2Budget 0 (localizedBeurling μ hμ f) ≤
            k * planeDerivativeL2Budget 0 f :=
        norm_localizedBeurling_toLp_le μ hμ hbound f
      nlinarith [congrArg (fun x : ℝ => k * x) hhigh,
        hprincipal h, hprincipal (∂_{(1 : ℂ)} h), hprincipal (∂_{I} h),
        hbound1 h, hboundI h]
  | succ m ih =>
      obtain ⟨C, hC, hprincipal⟩ := ih
      obtain ⟨C1, hC1, hbound1⟩ :=
        exists_localized_budget_bound (m + 1) (∂_{(1 : ℂ)} μ) hμ1
      obtain ⟨CI, hCI, hboundI⟩ :=
        exists_localized_budget_bound (m + 1) (∂_{I} μ) hμI
      refine ⟨C + C1 + CI, by positivity, fun h => ?_⟩
      have hproduct := localized_budget_succ_le (m + 1) μ h hμ hμ1 hμI
      have hhigh : planeDerivativeL2Budget (m + 1 + 1) h =
          planeDerivativeL2Budget (m + 1) h +
            planeDerivativeL2Budget (m + 1) (∂_{(1 : ℂ)} h) +
            planeDerivativeL2Budget (m + 1) (∂_{I} h) := rfl
      have hlow : planeDerivativeL2Budget (m + 1) h =
          planeDerivativeL2Budget m h + planeDerivativeL2Budget m (∂_{(1 : ℂ)} h) +
            planeDerivativeL2Budget m (∂_{I} h) := rfl
      nlinarith [congrArg (fun x : ℝ => k * x) hhigh,
        congrArg (fun x : ℝ => C * x) hlow,
        hprincipal h, hprincipal (∂_{(1 : ℂ)} h), hprincipal (∂_{I} h),
        hbound1 h, hboundI h]

def beltramiNeumannTerm (μ : 𝓢(ℂ, ℂ)) (hμ : HasCompactSupport (μ : ℂ → ℂ))
    (a : 𝓢(ℂ, ℂ)) : ℕ → 𝓢(ℂ, ℂ)
  | 0 => a
  | n + 1 => localizedBeurling μ hμ (beltramiNeumannTerm μ hμ a n)

theorem exists_geometric_beltramiNeumann_derivative_bounds
    (μ : 𝓢(ℂ, ℂ)) (hμ : HasCompactSupport (μ : ℂ → ℂ))
    {k : ℝ} (hk : k < 1) (hbound : ∀ z, ‖μ z‖ ≤ k) (a : 𝓢(ℂ, ℂ)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ,
      planeDerivativeL2Budget m (beltramiNeumannTerm μ hμ a n) ≤ A * r ^ n := by
  have hk0 : 0 ≤ k := (norm_nonneg (μ 0)).trans (hbound 0)
  let r := (k + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hkr : k < r := by dsimp [r]; linarith
  refine ⟨r, hr0, hr1, fun m => ?_⟩
  induction m with
  | zero =>
      refine ⟨planeDerivativeL2Budget 0 a, budget_nonneg 0 a, fun n => ?_⟩
      induction n with
      | zero => simp [beltramiNeumannTerm]
      | succ n ih =>
          calc
            _ ≤ k * planeDerivativeL2Budget 0 (beltramiNeumannTerm μ hμ a n) :=
              norm_localizedBeurling_toLp_le μ hμ hbound _
            _ ≤ k * (planeDerivativeL2Budget 0 a * r ^ n) :=
              mul_le_mul_of_nonneg_left ih hk0
            _ ≤ r * (planeDerivativeL2Budget 0 a * r ^ n) :=
              mul_le_mul_of_nonneg_right hkr.le
                (mul_nonneg (budget_nonneg 0 a) (pow_nonneg hr0.le _))
            _ = _ := by rw [pow_succ]; ring
  | succ m ih =>
      obtain ⟨A, hA, hAbound⟩ := ih
      obtain ⟨C, hC, hprincipal⟩ := exists_localized_principal_budget_bound m μ hμ hbound
      let B := max (planeDerivativeL2Budget (m + 1) a) (C * A / (r - k))
      have hB0 : 0 ≤ B := (budget_nonneg (m + 1) a).trans (le_max_left _ _)
      have hBinit : planeDerivativeL2Budget (m + 1) a ≤ B := le_max_left _ _
      have hBC : C * A ≤ B * (r - k) :=
        (div_le_iff₀ (sub_pos.mpr hkr)).mp (le_max_right _ _)
      have hcoef : k * B + C * A ≤ B * r := by nlinarith
      refine ⟨B, hB0, fun n => ?_⟩
      induction n with
      | zero => simpa [beltramiNeumannTerm] using hBinit
      | succ n ihn =>
          calc
            _ ≤ k * planeDerivativeL2Budget (m + 1) (beltramiNeumannTerm μ hμ a n) +
                C * planeDerivativeL2Budget m (beltramiNeumannTerm μ hμ a n) :=
              hprincipal _
            _ ≤ k * (B * r ^ n) + C * (A * r ^ n) :=
              _root_.add_le_add (mul_le_mul_of_nonneg_left ihn hk0)
                (mul_le_mul_of_nonneg_left (hAbound n) hC)
            _ = (k * B + C * A) * r ^ n := by ring
            _ ≤ (B * r) * r ^ n := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0.le _)
            _ = _ := by rw [pow_succ]; ring

end Complex
