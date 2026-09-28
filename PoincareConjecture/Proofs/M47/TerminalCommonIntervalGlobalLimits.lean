import PoincareConjecture.Proofs.M47.TerminalCommonIntervalGlobalRows
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalLimitIdentities
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

theorem terminalCommonInterval_composition_tendsto_of_rows
    {M N : Type u} [MetricSpace M] [MetricSpace N]
    (L : ℕ → Set N) (hcover : ∀ y, ∃ j, y ∈ interior (L j))
    (T : ℕ → M → N) (S : ℕ → N → M) (f : M → N) (g : N → M)
    (hg : Continuous g)
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (f x)))
    (hS : ∀ j, TendstoUniformlyOn S g atTop (L j)) :
    ∀ x, Tendsto (fun n => S n (T n x)) atTop (𝓝 (g (f x))) := by
  intro x
  obtain ⟨j, hj⟩ := hcover (f x)
  have hmem : ∀ᶠ n in atTop, T n x ∈ L j :=
    (hT x).eventually (mem_interior_iff_mem_nhds.mp hj)
  exact (hS j).tendsto_comp hg.continuousAt.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hT x, hmem⟩)

theorem terminalCommonInterval_global_inverse_limits
    {M N : Type u} [MetricSpace M] [MetricSpace N]
    (K : ℕ → Set M) (L : ℕ → Set N)
    (hKcover : ∀ x, ∃ j, x ∈ interior (K j))
    (hLcover : ∀ y, ∃ j, y ∈ interior (L j))
    (T : ℕ → OpenPartialHomeomorph M N) (f : M → N) (g : N → M)
    (hf : Continuous f) (hg : Continuous g)
    (hT : ∀ j, TendstoUniformlyOn (fun n => T n) f atTop (K j))
    (hS : ∀ j, TendstoUniformlyOn (fun n => (T n).symm) g atTop (L j))
    (hsource : ∀ x, ∀ᶠ n in atTop, x ∈ (T n).source)
    (htarget : ∀ y, ∀ᶠ n in atTop, y ∈ (T n).target)
    (p : M) (q : N) (hbase : ∀ᶠ n in atTop, T n p = q ∧ (T n).symm q = p) :
    Function.LeftInverse g f ∧ Function.RightInverse g f ∧ f p = q ∧ g q = p := by
  have hfpoint (x : M) : Tendsto (fun n => T n x) atTop (𝓝 (f x)) := by
    obtain ⟨j, hj⟩ := hKcover x
    exact (hT j).tendsto_at (interior_subset hj)
  have hgpoint (y : N) : Tendsto (fun n => (T n).symm y) atTop (𝓝 (g y)) := by
    obtain ⟨j, hj⟩ := hLcover y
    exact (hS j).tendsto_at (interior_subset hj)
  have hleft : Function.LeftInverse g f := terminalCommonInterval_limit_left_inverse f g
    (terminalCommonInterval_composition_tendsto_of_rows L hLcover
      (fun n => T n) (fun n => (T n).symm) f g hg hfpoint hS)
    (fun x => (hsource x).mono (fun n hn => (T n).left_inv hn))
  have hright : Function.RightInverse g f := terminalCommonInterval_limit_right_inverse f g
    (terminalCommonInterval_composition_tendsto_of_rows K hKcover
      (fun n => (T n).symm) (fun n => T n) g f hf hgpoint hT)
    (fun y => (htarget y).mono (fun n hn => (T n).right_inv hn))
  refine ⟨hleft, hright, ?_, ?_⟩
  · exact tendsto_nhds_unique (hfpoint p)
      (Filter.Tendsto.congr' (hbase.mono (fun _ hn => hn.1.symm)) tendsto_const_nhds)
  · exact tendsto_nhds_unique (hgpoint q)
      (Filter.Tendsto.congr' (hbase.mono (fun _ hn => hn.2.symm)) tendsto_const_nhds)

end PoincareConjecture.M47
