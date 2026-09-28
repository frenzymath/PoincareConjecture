import PoincareConjecture.Proofs.M47.TerminalCommonIntervalChartPairs
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalChartGlobalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_diffeomorph_of_actual_jets
    {M : Type u} {N : Type v} {X : ℕ → Type w}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    [MetricSpace N] [LocallyCompactSpace N]
    [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]
    [∀ n, TopologicalSpace (X n)] [∀ n, ChartedSpace E (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X n) ∞)
    (f : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) N (X n) ∞)
    (d : M ≃ₜ N)
    (hsource : ∀ K : Set M, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ ((e n).trans (f n).symm).source)
    (hsourceF : ∀ K : Set N, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).source)
    (hconv : ∀ K : Set M, IsCompact K → TendstoUniformlyOn
      (fun n => (e n).trans (f n).symm) d atTop K)
    (a : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (b : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) N E ∞)
    (ha : ∀ x : M, ∃ i, x ∈ (a i).source)
    (hb : ∀ y : N, ∃ j, y ∈ (b j).source)
    (hjetA : ∀ i m K, IsCompact K → K ⊆ (a i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m ((h n).pullbackCoefficients (e n ∘ (a i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (a i).symm)) atTop K)
    (hjetB : ∀ i m K, IsCompact K → K ⊆ (b i).target → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m ((h n).pullbackCoefficients (f n ∘ (b i).symm)))
      (iteratedFDeriv ℝ m (k.pullbackCoefficients (b i).symm)) atTop K) :
    let a' := fun i => a (Nat.unpair i).1
    let b' := fun i => b (Nat.unpair i).2
    let U := fun i => (a' i).target ∩ (a' i).symm ⁻¹' (d ⁻¹' (b' i).source)
    ∃ I : Diffeomorph (𝓡 3) (𝓡 3) M N ∞,
      (I : M → N) = d ∧ (I.symm : N → M) = d.symm ∧
      (∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
        g.inner x v w = k.inner (I x)
          (mfderiv (𝓡 3) (𝓡 3) I x v) (mfderiv (𝓡 3) (𝓡 3) I x w)) ∧
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
          (fun n => iteratedFDeriv ℝ m
            ((((a' i).symm.trans (e (sigma n))).trans (f (sigma n)).symm).trans (b' i)))
          (iteratedFDeriv ℝ m (fun x => b' i (d ((a' i).symm x)))) atTop K := by
  let a' := fun i => a (Nat.unpair i).1
  let b' := fun i => b (Nat.unpair i).2
  let U := fun i => (a' i).target ∩ (a' i).symm ⁻¹' (d ⁻¹' (b' i).source)
  obtain ⟨hU, hUa, hUb, hcover⟩ :=
    terminalCommonInterval_countable_chart_pairs d d.continuous a b ha hb
  obtain ⟨sigma, hsigma, hsmooth, _hmaps, hjets, hmetric⟩ :=
    terminalCommonInterval_actual_coordinate_extraction g k h e f d d.continuous
      hsource hsourceF hconv a' b' U hU hUa hUb
      (fun i => hjetA (Nat.unpair i).1) (fun i => hjetB (Nat.unpair i).2)
  obtain ⟨I, hI, hIinv, hinner⟩ :=
    terminalCommonInterval_diffeomorph_of_coordinate_rows a' b' U hU d g k
      hUb hcover hsmooth hmetric
  exact ⟨I, hI, hIinv, hinner, sigma, hsigma, hjets⟩

end PoincareConjecture.M47
