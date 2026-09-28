import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem mapsTo_ball_of_pathELength_lt
    (g : RiemannianMetric n M) (p : M) {r a b : ℝ}
    (hab : a ≤ b) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hγa : γ a = p)
    (hshort : g.pathELength γ a b < ENNReal.ofReal r) :
    MapsTo γ (Icc a b) (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro s hs
  change Manifold.riemannianEDist (𝓡 n) p (γ s) < ENNReal.ofReal r
  change Manifold.pathELength (𝓡 n) γ a b < ENNReal.ofReal r at hshort
  have hmono : Manifold.pathELength (𝓡 n) γ a s ≤
      Manifold.pathELength (𝓡 n) γ a b := by
    exact Manifold.pathELength_mono le_rfl hs.2
  have hdist : Manifold.riemannianEDist (𝓡 n) (γ a) (γ s) ≤
      Manifold.pathELength (𝓡 n) γ a s := by
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl hs.2)) rfl rfl hs.1
  have hchain : Manifold.riemannianEDist (𝓡 n) (γ a) (γ s) <
      ENNReal.ofReal r := by
    calc
      _ ≤ Manifold.pathELength (𝓡 n) γ a s := hdist
      _ ≤ Manifold.pathELength (𝓡 n) γ a b := hmono
      _ < ENNReal.ofReal r := hshort
  simpa [hγa] using hchain

end PoincareConjecture.RicciFlowAnalysis
