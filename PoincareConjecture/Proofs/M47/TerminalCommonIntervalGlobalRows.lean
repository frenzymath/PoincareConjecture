import PoincareConjecture.Proofs.M47.TerminalCommonIntervalGlueRows
import Mathlib.Topology.UniformSpace.CompactConvergence









set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

universe u

namespace PoincareConjecture.M47



theorem terminalCommonInterval_glue_convergent_rows
    {M N : Type u} [MetricSpace M] [MetricSpace N]
    (K : ℕ → Set M) (L : ℕ → Set N) [∀ j, CompactSpace (K j)]
    (hcover : ∀ x, ∃ j, x ∈ interior (K j))
    (T : ℕ → M → N) (F : ∀ j, ℕ → C(K j, L j))
    (f : ∀ j, C(K j, L j)) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (hactual : ∀ j, ∀ᶠ n in atTop, ∀ x : K j, (F j n x).val = T n x)
    (hconv : ∀ j, Tendsto (F j ∘ rho) atTop (𝓝 (f j))) :
    ∃ t : M → N, Continuous t ∧
      (∀ j (x : K j), t x = (f j x).val) ∧
      ∀ j, TendstoUniformlyOn (fun n => T (rho n)) t atTop (K j) := by
  have huniform (j : ℕ) : TendstoUniformly
      (fun n (x : K j) => T (rho n) x) (fun x => (f j x).val) atTop := by
    have hc := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hconv j)
    have hu := uniformContinuous_subtype_val.comp_tendstoUniformly hc
    apply (tendstoUniformly_congr ?_).mp hu
    filter_upwards [hrho.tendsto_atTop.eventually (hactual j)] with n hn
    funext x
    exact hn x
  have hcompat : ∀ i j (x : M) (hi : x ∈ K i) (hj : x ∈ K j),
      (f i ⟨x, hi⟩).val = (f j ⟨x, hj⟩).val := by
    intro i j x hi hj
    exact tendsto_nhds_unique ((huniform i).tendsto_at ⟨x, hi⟩)
      ((huniform j).tendsto_at ⟨x, hj⟩)
  obtain ⟨t, ht, hread⟩ := terminalCommonInterval_glue_row_limits K L hcover f hcompat
  refine ⟨t, ht, hread, ?_⟩
  intro j
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have heq : (t ∘ (Subtype.val : K j → M)) = fun x : K j => (f j x).val :=
    funext (hread j)
  rw [heq]
  exact huniform j



theorem terminalCommonInterval_global_paired_limits
    {M N : Type u} [MetricSpace M] [MetricSpace N]
    (K K' : ℕ → Set M) (L L' : ℕ → Set N)
    [∀ j, CompactSpace (K j)] [∀ j, CompactSpace (K' j)]
    [∀ j, CompactSpace (L j)] [∀ j, CompactSpace (L' j)]
    (hKcover : ∀ x, ∃ j, x ∈ interior (K j))
    (hLcover : ∀ y, ∃ j, y ∈ interior (L j))
    (p : M) (q : N) (hp : ∀ j, p ∈ K' j) (hq : ∀ j, q ∈ L' j)
    (C : ℝ≥0) (T : ℕ → M → N) (S : ℕ → N → M)
    (hT : ∀ j, ∀ᶠ n in atTop, MapsTo (T n) (K j) (L' j) ∧
      LipschitzOnWith C (T n) (K j))
    (hS : ∀ j, ∀ᶠ n in atTop, MapsTo (S n) (L j) (K' j) ∧
      LipschitzOnWith C (S n) (L j)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ (t : M → N) (s : N → M),
      Continuous t ∧ Continuous s ∧
      (∀ j, TendstoUniformlyOn (fun n => T (rho n)) t atTop (K j)) ∧
      (∀ j, TendstoUniformlyOn (fun n => S (rho n)) s atTop (L j)) := by
  obtain ⟨F, hF, hFactual⟩ := terminalCommonInterval_captured_rows K L' q hq C T hT
  obtain ⟨H, hH, hHactual⟩ := terminalCommonInterval_captured_rows L K' p hp C S hS
  obtain ⟨f, h, _hlip, rho, hrho, hconv⟩ :=
    terminalCommonInterval_paired_row_subsequence C F H
      (fun j => Eventually.of_forall (hF j)) (fun j => Eventually.of_forall (hH j))
  obtain ⟨t, ht, _htread, htconv⟩ := terminalCommonInterval_glue_convergent_rows
    K L' hKcover T F f rho hrho hFactual (fun j => (hconv j).1)
  obtain ⟨s, hs, _hsread, hsconv⟩ := terminalCommonInterval_glue_convergent_rows
    L K' hLcover S H h rho hrho hHactual (fun j => (hconv j).2)
  exact ⟨rho, hrho, t, s, ht, hs, htconv, hsconv⟩

end PoincareConjecture.M47
