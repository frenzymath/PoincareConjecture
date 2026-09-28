import PoincareConjecture.Proofs.M03.Existence.VolterraPicard
import PoincareConjecture.Proofs.M03.Existence.VolterraContractionNative












set_option autoImplicit false

open Set MeasureTheory

namespace PoincareConjecture

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]




structure DuhamelSource (T : ℝ) where
  field : ℝ → E
  continuous : ContinuousOn field (Ico (0 : ℝ) T)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  field_bound : ∀ s ∈ Ico (0 : ℝ) T, ‖field s‖ ≤ bound

namespace DuhamelSource

variable {T : ℝ} (S : DuhamelSource (E := E) T)


noncomputable def path (x₀ : E) (t : ℝ) : E :=
  x₀ + ∫ s in (0 : ℝ)..t, S.field s

@[simp] theorem path_zero (x₀ : E) : S.path x₀ 0 = x₀ := by
  simp [path]

theorem path_eq_volterraPath (x₀ : E) :
    S.path x₀ = volterraPath x₀ S.field := by
  rfl

theorem hasDerivWithinAt_path
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x₀ : E) :
    HasDerivWithinAt (S.path x₀) (S.field t) (Ico (0 : ℝ) T) t := by
  exact hasDerivWithinAt_volterraPath_Ico S.continuous ht

theorem path_sub_initial_norm_le
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x₀ : E) :
    ‖S.path x₀ t - x₀‖ ≤ S.bound * t := by
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) t, ‖S.field x‖ ≤ S.bound := by
    intro x hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) t := by
      simpa only [uIoc_of_le ht.1] using hx
    have hx0 : 0 ≤ x := hx'.1.le
    have hxt : x < T := lt_of_le_of_lt hx'.2 ht.2
    exact S.field_bound x ⟨hx0, hxt⟩
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hrepr : S.path x₀ t - x₀ = ∫ s in (0 : ℝ)..t, S.field s := by
    simp [path]
  rw [hrepr]
  simpa [abs_of_nonneg ht.1] using hint

theorem path_distance_le
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x₀ : E) :
    dist (S.path x₀ t) x₀ ≤ S.bound * t := by
  simpa only [dist_eq_norm, norm_sub_rev] using S.path_sub_initial_norm_le ht x₀

end DuhamelSource




structure DuhamelStateSource (T : ℝ) where
  field : ℝ → E → E
  continuous : ContinuousOn (Function.uncurry field)
      ((Ico (0 : ℝ) T) ×ˢ Set.univ)
  lipschitz : ℝ
  lipschitz_nonneg : 0 ≤ lipschitz
  lipschitz_bound : ∀ s ∈ Ico (0 : ℝ) T, ∀ x y,
    ‖field s x - field s y‖ ≤ lipschitz * ‖x - y‖

namespace DuhamelStateSource

variable {T : ℝ} (S : DuhamelStateSource (E := E) T)


noncomputable def operator (x₀ : E) (u : ℝ → E) (t : ℝ) : E :=
  x₀ + ∫ s in (0 : ℝ)..t, S.field s (u s)

@[simp] theorem operator_zero (x₀ : E) (u : ℝ → E) :
    S.operator x₀ u 0 = x₀ := by
  simp [operator]

theorem operator_sub_operator_norm_le
    {u v : ℝ → E} {t B : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (hB : ∀ s ∈ Icc (0 : ℝ) t, ‖u s - v s‖ ≤ B)
    (hu : IntervalIntegrable (fun s => S.field s (u s)) volume 0 t)
    (hv : IntervalIntegrable (fun s => S.field s (v s)) volume 0 t) :
    ‖S.operator 0 u t - S.operator 0 v t‖ ≤ S.lipschitz * B * t := by
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖S.field s (u s) - S.field s (v s)‖ ≤
        S.lipschitz * B := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) t := by
      have hs' : s ∈ Set.Ioc (0 : ℝ) t := by
        simpa only [uIoc_of_le ht.1] using hs
      exact ⟨hs'.1.le, hs'.2⟩
    have hsT : s ∈ Ico (0 : ℝ) T := by
      refine ⟨hsI.1, ?_⟩
      exact lt_of_le_of_lt hsI.2 ht.2
    calc
      ‖S.field s (u s) - S.field s (v s)‖ ≤
          S.lipschitz * ‖u s - v s‖ := S.lipschitz_bound s hsT _ _
      _ ≤ S.lipschitz * B :=
        mul_le_mul_of_nonneg_left (hB s hsI) S.lipschitz_nonneg
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hrepr : S.operator 0 u t - S.operator 0 v t =
      ∫ s in (0 : ℝ)..t, S.field s (u s) - S.field s (v s) := by
    simp only [operator, zero_add, zero_sub]
    rw [intervalIntegral.integral_sub hu hv]
  rw [hrepr]
  simpa [abs_of_nonneg ht.1, mul_assoc, mul_left_comm, mul_comm] using hint

theorem operator_fixed_path
    (x₀ : E) (u : ℝ → E) (hfix : ∀ t, S.operator x₀ u t = u t) :
    ∀ t, u t = x₀ + ∫ s in (0 : ℝ)..t, S.field s (u s) := by
  intro t
  exact (hfix t).symm

end DuhamelStateSource

end PoincareConjecture
