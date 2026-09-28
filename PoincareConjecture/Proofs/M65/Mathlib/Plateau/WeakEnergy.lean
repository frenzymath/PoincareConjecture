import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic











set_option autoImplicit false

open Filter
open scoped Topology

namespace InnerProductSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {l : Filter ι}




theorem tendsto_inner_of_bounded_weak_of_tendsto
    {u v : ι → E} {u0 v0 : E} {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hweak : ∀ w : E, Tendsto (fun i => ⟪u i, w⟫_ℝ) l (𝓝 ⟪u0, w⟫_ℝ))
    (hv : Tendsto v l (𝓝 v0)) :
    Tendsto (fun i => ⟪u i, v i⟫_ℝ) l (𝓝 ⟪u0, v0⟫_ℝ) := by
  have hsmall : Tendsto (fun i => ⟪u i, v i - v0⟫_ℝ) l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun i => C * ‖v i - v0‖)
    · filter_upwards [hbound] with i hi
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    · simpa only [sub_self, norm_zero, mul_zero] using
        (tendsto_const_nhds.mul (hv.sub tendsto_const_nhds).norm :
          Tendsto (fun i => C * ‖v i - v0‖) l (𝓝 (C * ‖v0 - v0‖)))
  have hsum := hsmall.add (hweak v0)
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using hsum




theorem tendsto_inner_apply_of_adjoint_tendsto [CompleteSpace E] [CompleteSpace F]
    {u : ι → E} {u0 : E} {C : ℝ} {A : ι → E →L[ℝ] F} {A0 : E →L[ℝ] F}
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hweak : ∀ w : E, Tendsto (fun i => ⟪u i, w⟫_ℝ) l (𝓝 ⟪u0, w⟫_ℝ))
    (hA : ∀ w : F, Tendsto (fun i => (A i).adjoint w) l (𝓝 (A0.adjoint w)))
    (w : F) :
    Tendsto (fun i => ⟪A i (u i), w⟫_ℝ) l (𝓝 ⟪A0 u0, w⟫_ℝ) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using
    tendsto_inner_of_bounded_weak_of_tendsto hbound hweak (hA w)




theorem norm_sq_le_of_tendsto_inner_of_tendsto_norm_sq [NeBot l]
    {u : ι → E} {u0 : E} {energy : ℝ}
    (hweak : Tendsto (fun i => ⟪u i, u0⟫_ℝ) l (𝓝 ⟪u0, u0⟫_ℝ))
    (henergy : Tendsto (fun i => ‖u i‖ ^ 2) l (𝓝 energy)) :
    ‖u0‖ ^ 2 ≤ energy := by
  have hle (i : ι) : 2 * ⟪u i, u0⟫_ℝ - ‖u0‖ ^ 2 ≤ ‖u i‖ ^ 2 := by
    have hn := sq_nonneg ‖u i - u0‖
    rw [norm_sub_sq_real] at hn
    linarith
  have hlim := le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.mul hweak).sub tendsto_const_nhds) henergy
    (Eventually.of_forall hle)
  rw [real_inner_self_eq_norm_sq] at hlim
  linarith





theorem norm_sq_apply_le_of_adjoint_tendsto [CompleteSpace E] [CompleteSpace F]
    [NeBot l] {u : ι → E} {u0 : E} {C energy : ℝ}
    {A : ι → E →L[ℝ] F} {A0 : E →L[ℝ] F}
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hweak : ∀ w : E, Tendsto (fun i => ⟪u i, w⟫_ℝ) l (𝓝 ⟪u0, w⟫_ℝ))
    (hA : ∀ w : F, Tendsto (fun i => (A i).adjoint w) l (𝓝 (A0.adjoint w)))
    (henergy : Tendsto (fun i => ‖A i (u i)‖ ^ 2) l (𝓝 energy)) :
    ‖A0 u0‖ ^ 2 ≤ energy :=
  norm_sq_le_of_tendsto_inner_of_tendsto_norm_sq
    (tendsto_inner_apply_of_adjoint_tendsto hbound hweak hA (A0 u0)) henergy

end InnerProductSpace
