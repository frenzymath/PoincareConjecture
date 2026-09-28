import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

namespace Poincare.GromovHausdorff

universe u

theorem exists_subseq_finite_pointConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (S : VaryingRealizationSequence
      (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
    {ρ σ : ℝ} (hρσ : ρ < σ) (hcompact : IsCompact (Metric.closedBall Y.base σ))
    {k : ℕ} (x : ∀ j, Fin k → (X j).carrier)
    (hx : ∀ j i, dist (X j).base (x j i) ≤ ρ) :
    ∃ y : Fin k → Y.carrier, (∀ i, dist Y.base (y i) ≤ ρ) ∧
      ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ), ∀ i,
        (S.comp φ hφ.tendsto_atTop).PointConverges (fun j => x (φ j) i) (y i) := by
  induction k generalizing X with
  | zero =>
      refine ⟨Fin.elim0, ?_, id, strictMono_id, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ k ih =>
      obtain ⟨_, _, y₀, hy₀, φ, hφ, hconv₀⟩ :=
        exists_approximating_maps_and_subseq_pointConverges S hρσ hcompact
          (fun j => x j 0) (fun j => hx j 0)
      obtain ⟨y, hy, ψ, hψ, hconv⟩ :=
        ih (S.comp φ hφ.tendsto_atTop)
          (fun j i => x (φ j) i.succ) (fun j i => hx (φ j) i.succ)
      refine ⟨Fin.cons y₀ y, ?_, φ ∘ ψ, hφ.comp hψ, ?_⟩
      · exact Fin.cases hy₀ hy
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · exact Filter.Tendsto.comp hconv₀ hψ.tendsto_atTop
        · exact hconv i

end Poincare.GromovHausdorff
