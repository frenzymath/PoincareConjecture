import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Flow

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

def RicciFlow.openAncientRescaleAt
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (F : RicciFlow n N (Iio 0)) (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) :
    RicciFlow n N (Iio (-t₀ * Q)) :=
  F.parabolicRescale Q hQ t₀
    (fun s hs => by
      have h := (div_lt_iff₀ hQ).mpr hs
      change t₀ + s / Q < 0
      linarith)
    ordConnected_Iio ⟨-t₀ * Q - 2, by simp, -t₀ * Q - 1, by simp, by linarith⟩

end PoincareConjecture
