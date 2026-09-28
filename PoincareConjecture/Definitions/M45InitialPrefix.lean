import PoincareConjecture.Definitions.M45ControlledSchedules










set_option autoImplicit false

universe u

namespace PoincareConjecture.RepairedControlledSchedulesData

variable (B : RepairedControlledSchedulesData.{u})

theorem Delta0_pos : 0 < B.Delta0 := by
  rw [B.calibration.delta_zero_eq]
  exact lt_min
    (div_pos (mul_pos B.calibration.beta_pos B.setup.epsilon_pos) (by norm_num))
    (lt_min B.calibration.delta₁₃_pos
      (lt_min (inv_pos.mpr B.cap_persistence.standard_cap.initial_estimate.core_volume_constant_pos)
        (inv_pos.mpr B.cap_persistence.standard_cap.initial_estimate.scalar_constant_pos)))

theorem Delta0_le_setup : B.Delta0 ≤ B.constants.delta₀ := by
  rw [B.calibration.delta_zero_eq]
  exact (min_le_right _ _).trans ((min_le_left _ _).trans B.calibration.delta₁₃_le)



def initialPrefix : SurgeryParameterPrefix B.constants where
  setup := B.setup
  i := 1
  i_pos := Nat.zero_lt_succ 0
  r := fun _ => B.setup.epsilon
  kappa := fun _ => B.kappa0
  Delta := fun _ => B.Delta0
  r_pos := fun _ => B.setup.epsilon_pos
  kappa_pos := fun _ => B.calibration.kappa₀_pos
  Delta_pos := fun _ => B.Delta0_pos
  r_antitone := fun {_ _} _ => le_rfl
  kappa_antitone := fun {_ _} _ => le_rfl
  Delta_antitone := fun {_ _} _ => le_rfl
  r_zero := rfl
  r_le_epsilon := fun _ => le_rfl
  Delta_le_setup := fun _ => B.Delta0_le_setup

@[simp] theorem initialPrefix_i : B.initialPrefix.i = 1 := rfl

@[simp] theorem initialPrefix_setup : B.initialPrefix.setup = B.setup := rfl

@[simp] theorem initialPrefix_r (j : Fin 2) :
    B.initialPrefix.r j = B.setup.epsilon := rfl

@[simp] theorem initialPrefix_kappa (j : Fin 2) :
    B.initialPrefix.kappa j = B.kappa0 := rfl

@[simp] theorem initialPrefix_Delta (j : Fin 2) :
    B.initialPrefix.Delta j = B.Delta0 := rfl

theorem initialPrefix_seedCompatible : B.SeedCompatible B.initialPrefix :=
  ⟨rfl, rfl, rfl⟩




noncomputable def restrictDelta (d : ℝ) (hd : 0 < d) :
    RepairedControlledSchedulesData.{u} := by
  have hdelta : 0 < min B.Delta0 d := lt_min B.Delta0_pos hd
  have hrho : 0 ≤ min B.Delta0 d * B.setup.epsilon :=
    mul_nonneg hdelta.le B.setup.epsilon_pos.le
  have hrho_old : 0 ≤ B.Delta0 * B.setup.epsilon :=
    mul_nonneg B.Delta0_pos.le B.setup.epsilon_pos.le
  have hdelta_mono :
      B.setup.selector.h (min B.Delta0 d * B.setup.epsilon) (min B.Delta0 d) ≤
        B.setup.selector.h (min B.Delta0 d * B.setup.epsilon) B.Delta0 :=
    B.setup.selector.h_mono_delta _ hrho hdelta.le B.Delta0_pos.le (min_le_left _ _)
  have hrho_mono :
      B.setup.selector.h (min B.Delta0 d * B.setup.epsilon) B.Delta0 ≤
        B.setup.selector.h (B.Delta0 * B.setup.epsilon) B.Delta0 :=
    B.setup.selector.h_mono_rho _ B.Delta0_pos.le hrho hrho_old
      (mul_le_mul_of_nonneg_right (min_le_left _ _) B.setup.epsilon_pos.le)
  exact { B with
    Delta0 := min B.Delta0 d
    calibration := { B.calibration with
      delta₁₃ := min B.calibration.delta₁₃ d
      delta₁₃_pos := lt_min B.calibration.delta₁₃_pos hd
      delta₁₃_le := (min_le_left _ _).trans B.calibration.delta₁₃_le
      delta_zero_eq := by
        exact (congrArg (fun z : ℝ => min z d)
          B.calibration.delta_zero_eq).trans (by ac_rfl)
      selector_initial_bound :=
        hdelta_mono.trans (hrho_mono.trans B.calibration.selector_initial_bound) } }

variable (d : ℝ) (hd : 0 < d)

@[simp] theorem restrictDelta_constants :
    (B.restrictDelta d hd).constants = B.constants := rfl

@[simp] theorem restrictDelta_setup :
    (B.restrictDelta d hd).setup = B.setup := rfl

@[simp] theorem restrictDelta_kappa0 :
    (B.restrictDelta d hd).kappa0 = B.kappa0 := rfl

@[simp] theorem restrictDelta_Delta0 :
    (B.restrictDelta d hd).Delta0 = min B.Delta0 d := rfl

@[simp] theorem restrictDelta_standard_initial :
    (B.restrictDelta d hd).standard_initial = B.standard_initial := rfl

@[simp] theorem restrictDelta_cap_persistence :
    (B.restrictDelta d hd).cap_persistence = B.cap_persistence := rfl

@[simp] theorem restrictDelta_appendixA :
    (B.restrictDelta d hd).calibration.appendixA = B.calibration.appendixA := rfl

@[simp] theorem restrictDelta_common_epsilon :
    (B.restrictDelta d hd).calibration.common_epsilon = B.calibration.common_epsilon := rfl

@[simp] theorem restrictDelta_delta13 :
    (B.restrictDelta d hd).calibration.delta₁₃ = min B.calibration.delta₁₃ d := rfl

end PoincareConjecture.RepairedControlledSchedulesData
