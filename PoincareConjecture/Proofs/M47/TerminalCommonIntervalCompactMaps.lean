import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology NNReal

universe u v

namespace PoincareConjecture.M47



theorem terminalCommonInterval_isCompact_lipschitz_maps
    {A : Type u} {B : Type v} [MetricSpace A] [MetricSpace B] [CompactSpace B]
    (L : ℝ≥0) : IsCompact {f : C(A, B) | LipschitzWith L f} := by
  let S : Set C(A, B) := {f | LipschitzWith L f}
  have himage : ContinuousMap.toFun '' S = {f : A → B | LipschitzWith L f} := by
    ext f
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact hF
    · intro hf
      exact ⟨⟨f, hf.continuous⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous S
  · rw [himage]
    exact (isClosed_setOfPred_lipschitzWith L).isCompact
  · exact (Metric.uniformEquicontinuous_of_continuity_modulus
      (fun r : ℝ => (L : ℝ) * r) (by
        have hc : Tendsto (fun _ : ℝ => (L : ℝ)) (𝓝 0) (𝓝 (L : ℝ)) :=
          tendsto_const_nhds
        convert hc.mul (tendsto_id'.mpr le_rfl) using 1 <;>
          simp [mul_zero])
      (fun f : S => (f.val : A → B)) (fun x y f => f.property.dist_le_mul x y)).equicontinuous



theorem terminalCommonInterval_compact_row_subsequence
    {A : ℕ → Type u} {B : ℕ → Type v}
    [∀ j, MetricSpace (A j)] [∀ j, MetricSpace (B j)]
    [∀ j, CompactSpace (A j)] [∀ j, CompactSpace (B j)]
    (L : ℝ≥0) (F : ∀ j, ℕ → C(A j, B j))
    (hF : ∀ j, ∀ᶠ n in atTop, LipschitzWith L (F j n)) :
    ∃ f : ∀ j, C(A j, B j), (∀ j, LipschitzWith L (f j)) ∧
      ∃ rho : ℕ → ℕ, StrictMono rho ∧
        ∀ j, Tendsto (F j ∘ rho) atTop (𝓝 (f j)) := by
  exact Poincare.exists_strictMono_tendsto_of_eventually_mem_isCompact F
    (fun j => {f : C(A j, B j) | LipschitzWith L f})
    (fun _ => terminalCommonInterval_isCompact_lipschitz_maps L) hF



theorem terminalCommonInterval_paired_row_subsequence
    {A D : ℕ → Type u} {B E : ℕ → Type v}
    [∀ j, MetricSpace (A j)] [∀ j, MetricSpace (B j)]
    [∀ j, MetricSpace (D j)] [∀ j, MetricSpace (E j)]
    [∀ j, CompactSpace (A j)] [∀ j, CompactSpace (B j)]
    [∀ j, CompactSpace (D j)] [∀ j, CompactSpace (E j)]
    (L : ℝ≥0) (F : ∀ j, ℕ → C(A j, B j)) (H : ∀ j, ℕ → C(D j, E j))
    (hF : ∀ j, ∀ᶠ n in atTop, LipschitzWith L (F j n))
    (hH : ∀ j, ∀ᶠ n in atTop, LipschitzWith L (H j n)) :
    ∃ f : ∀ j, C(A j, B j), ∃ h : ∀ j, C(D j, E j),
      (∀ j, LipschitzWith L (f j) ∧ LipschitzWith L (h j)) ∧
      ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ j,
        Tendsto (F j ∘ rho) atTop (𝓝 (f j)) ∧
        Tendsto (H j ∘ rho) atTop (𝓝 (h j)) := by
  obtain ⟨a, ha, rho, hrho, hlim⟩ :=
    Poincare.exists_strictMono_tendsto_of_eventually_mem_isCompact
      (fun j n => (F j n, H j n))
      (fun j => {f : C(A j, B j) | LipschitzWith L f} ×ˢ
        {h : C(D j, E j) | LipschitzWith L h})
      (fun _ => (terminalCommonInterval_isCompact_lipschitz_maps L).prod
        (terminalCommonInterval_isCompact_lipschitz_maps L))
      (fun j => (hF j).and (hH j))
  refine ⟨fun j => (a j).1, fun j => (a j).2, ha, rho, hrho, ?_⟩
  intro j
  have hp := hlim j
  rw [nhds_prod_eq] at hp
  exact ⟨by simpa only [Function.comp_def] using hp.fst,
    by simpa only [Function.comp_def] using hp.snd⟩

end PoincareConjecture.M47
