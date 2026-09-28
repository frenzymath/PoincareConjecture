import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M65Perturbation

private theorem nonincrease_of_upperRight (A : ℝ → ℝ) {s t : ℝ} (hst : s ≤ t)
    (hA : ContinuousOn A (Icc s t))
    (hupper : ∀ q ∈ Ico s t, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (A (q + h) - A q) / h ≤ epsilon) :
    A t ≤ A s := by
  have hfreq : ∀ q ∈ Ico s t, ∀ v : ℝ, 0 < v →
      ∃ᶠ y in 𝓝[>] q, slope A q y < v := by
    intro q hq v hv
    have hshift : Tendsto (fun y : ℝ => y - q) (𝓝[>] q) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : ContinuousAt (fun y : ℝ => y - q) q := by fun_prop
        simpa only [sub_self] using hc.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi q))
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_pos.mpr (show q < y from hy)
    apply Filter.Eventually.frequently
    filter_upwards [hshift.eventually (hupper q hq (v / 2) (half_pos hv))] with y hy
    have heq : q + (y - q) = y := by ring
    rw [heq] at hy
    rw [slope_def_field]
    linarith
  have hle : ∀ ⦃q⦄, q ∈ Icc s t → A q ≤ A s :=
    image_le_of_liminf_slope_right_le_deriv_boundary hA le_rfl continuousOn_const
      (fun q _ => hasDerivWithinAt_const q (Ici q) (A s)) hfreq
  exact hle ⟨hst, le_rfl⟩

private theorem nonincrease_of_upperRight_interior (A : ℝ → ℝ) {s t : ℝ} (hst : s ≤ t)
    (hA : ContinuousOn A (Icc s t))
    (hupper : ∀ q ∈ Ioo s t, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (A (q + h) - A q) / h ≤ epsilon) :
    A t ≤ A s := by
  rcases hst.eq_or_lt with heq | hst
  · subst t
    exact le_rfl
  have hle (u : ℝ) (hu : u ∈ Ioo s t) : A t ≤ A u :=
    nonincrease_of_upperRight A hu.2.le
      (hA.mono (fun _ hq => ⟨hu.1.le.trans hq.1, hq.2⟩))
      (fun q hq => hupper q ⟨hu.1.trans_le hq.1, hq.2⟩)
  have hclosure : s ∈ closure (Ioo s t) := by
    rw [closure_Ioo hst.ne]
    exact ⟨le_rfl, hst.le⟩
  exact ContinuousWithinAt.closure_le hclosure continuousWithinAt_const
    ((hA s ⟨le_rfl, hst.le⟩).mono Ioo_subset_Icc_self) hle





theorem nonincrease_of_upperRight_finite (A : ℝ → ℝ) (E : Finset ℝ)
    {s t : ℝ} (hst : s ≤ t) (hA : ContinuousOn A (Icc s t))
    (hupper : ∀ q ∈ Ioo s t, q ∉ E → ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (A (q + h) - A q) / h ≤ epsilon) :
    A t ≤ A s := by
  classical
  induction E using Finset.induction_on generalizing s t with
  | empty =>
      exact nonincrease_of_upperRight_interior A hst hA
        (fun q hq => hupper q hq (Finset.notMem_empty q))
  | @insert c E _ ih =>
      by_cases hc : c ∈ Ioo s t
      · have hleft : A c ≤ A s := ih hc.1.le
          (hA.mono (fun _ hq => ⟨hq.1, hq.2.trans hc.2.le⟩)) (by
            intro q hq hnot
            apply hupper q ⟨hq.1, hq.2.trans hc.2⟩
            simp only [Finset.mem_insert, not_or]
            exact ⟨hq.2.ne, hnot⟩)
        have hright : A t ≤ A c := ih hc.2.le
          (hA.mono (fun _ hq => ⟨hc.1.le.trans hq.1, hq.2⟩)) (by
            intro q hq hnot
            apply hupper q ⟨hc.1.trans hq.1, hq.2⟩
            simp only [Finset.mem_insert, not_or]
            exact ⟨hq.1.ne', hnot⟩)
        exact hright.trans hleft
      · apply ih hst hA
        intro q hq hnot
        apply hupper q hq
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun heq => hc (heq ▸ hq), hnot⟩

end PoincareConjecture.M65Perturbation
