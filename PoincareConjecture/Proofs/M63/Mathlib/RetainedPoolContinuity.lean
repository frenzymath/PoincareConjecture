import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Filter
open scoped Topology

universe u v w z

namespace PoincareConjecture.M63

theorem continuous_of_approximating_pool_subsequences
    {K : Type u} [TopologicalSpace K] [SequentialSpace K]
    {J : Type v} [PseudoMetricSpace J]
    {Y : Type w} [PseudoMetricSpace Y] {I : Type z}
    (Q : K → J) (hQ : Continuous Q) (p : I → J) (f : I → Y) (G : K → Y)
    (happrox : ∀ k, ∃ j : ℕ → I,
      Tendsto (fun n => p (j n)) atTop (𝓝 (Q k)) ∧
      Tendsto (fun n => f (j n)) atTop (𝓝 (G k)))
    (hsubseq : ∀ k, ∀ j : ℕ → I,
      Tendsto (fun n => p (j n)) atTop (𝓝 (Q k)) →
        ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
          Tendsto (fun n => f (j (sigma n))) atTop (𝓝 (G k))) :
    Continuous G := by
  classical
  have happ : ∀ k (eps : ℝ), 0 < eps →
      ∃ i, dist (p i) (Q k) < eps ∧ dist (f i) (G k) < eps := by
    intro k eps heps
    obtain ⟨j, hp, hf⟩ := happrox k
    obtain ⟨n, hpn, hfn⟩ :=
      ((Metric.tendsto_nhds.mp hp eps heps).and
        (Metric.tendsto_nhds.mp hf eps heps)).exists
    exact ⟨j n, hpn, hfn⟩
  apply continuous_iff_seqContinuous.mpr
  intro seq k hseq
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have heps : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    positivity
  choose alpha hap haf using fun n => happ (seq (ns n)) _ (heps n)
  have hpd : Tendsto (fun n => dist (p (alpha n)) (Q (seq (ns n))))
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hap n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hfd : Tendsto (fun n => dist (f (alpha n)) (G (seq (ns n))))
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (haf n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hQseq : Tendsto (fun n => Q (seq (ns n))) atTop (𝓝 (Q k)) :=
    (hQ.tendsto k).comp (hseq.comp hns)
  have hpseq : Tendsto (fun n => p (alpha n)) atTop (𝓝 (Q k)) :=
    hQseq.congr_dist (by simpa only [dist_comm] using hpd)
  obtain ⟨sigma, hsigma, hlimit⟩ := hsubseq k alpha hpseq
  exact ⟨sigma, hlimit.congr_dist (hfd.comp hsigma.tendsto_atTop)⟩

end PoincareConjecture.M63
