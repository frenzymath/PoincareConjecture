import PoincareConjecture.Proofs.M47.TerminalGermsEndpoint
import Mathlib.Analysis.Normed.Group.Continuity

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M47

theorem terminalGerms_uniform_endpoint_bound
    {X F : Type*} [NormedAddCommGroup F]
    {U : Set X} {a C : ℝ} (f : ℕ → ℝ × X → F)
    (B0 : X → F) (Bminus : ℝ × X → F)
    (hzero : ∀ x ∈ U, Tendsto (fun k => f k (0, x)) atTop (𝓝 (B0 x)))
    (hminus : ∀ t ∈ Ioo a 0, ∀ x ∈ U,
      Tendsto (fun k => f k (t, x)) atTop (𝓝 (Bminus (t, x))))
    (hbound : ∀ t ∈ Ioo a 0, ∀ x ∈ U,
      ∀ᶠ k in atTop, ‖f k (t, x) - f k (0, x)‖ ≤ C * |t|) :
    ∀ t ∈ Ioo a 0, ∀ x ∈ U, ‖Bminus (t, x) - B0 x‖ ≤ C * |t| := by
  intro t ht x hx
  exact le_of_tendsto (((hminus t ht x hx).sub (hzero x hx)).norm) (hbound t ht x hx)

theorem terminalGerms_joint_endpoint_continuity
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    {U : Set X} {a C : ℝ} (B0 : X → F) (Bminus : ℝ × X → F) (x0 : X)
    (hB0 : ContinuousWithinAt B0 U x0)
    (hbound : ∀ t ∈ Ioo a 0, ∀ x ∈ U, ‖Bminus (t, x) - B0 x‖ ≤ C * |t|) :
    ContinuousWithinAt
      (fun p : ℝ × X => if p.1 < 0 then Bminus p else B0 p.2)
      (Ioc a 0 ×ˢ U) (0, x0) := by
  let G : ℝ × X → F := fun p => if p.1 < 0 then Bminus p else B0 p.2
  let l := 𝓝[Ioc a 0 ×ˢ U] (0, x0)
  have hfirst : Tendsto (fun p : ℝ × X => p.1) l (𝓝 0) :=
    (continuous_fst.tendsto (0, x0)).mono_left inf_le_left
  have hsecond : Tendsto (fun p : ℝ × X => p.2) l (𝓝[U] x0) := by
    dsimp [l]
    rw [nhdsWithin_prod_eq]
    exact tendsto_snd
  have hterminal : Tendsto (fun p : ℝ × X => B0 p.2) l (𝓝 (B0 x0)) :=
    Tendsto.comp hB0 hsecond
  have hupper : Tendsto (fun p : ℝ × X => C * |p.1| + ‖B0 p.2 - B0 x0‖)
      l (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ × X => C) l (𝓝 C)).mul
      hfirst.abs).add ((hterminal.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ × X => B0 x0) l (𝓝 (B0 x0)))).norm)
  have hG0 : G (0, x0) = B0 x0 := by simp [G]
  change Tendsto G l (𝓝 (G (0, x0)))
  rw [hG0, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hpoint : ‖G p - B0 p.2‖ ≤ C * |p.1| := by
    by_cases ht : p.1 < 0
    · simpa only [G, if_pos ht] using hbound p.1 ⟨hp.1.1, ht⟩ p.2 hp.2
    · have ht0 : p.1 = 0 := le_antisymm hp.1.2 (le_of_not_gt ht)
      simp only [G, if_neg ht, sub_self, norm_zero, ht0, abs_zero, mul_zero, le_refl]
  exact (norm_sub_le_norm_sub_add_norm_sub (G p) (B0 p.2) (B0 x0)).trans
    (add_le_add hpoint le_rfl)

end PoincareConjecture.M47
