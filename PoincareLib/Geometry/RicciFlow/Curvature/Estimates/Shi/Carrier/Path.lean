import PoincareLib.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04/ShiPathCarrier.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Prefix retention for short paths

Every prefix of a path whose total length is below a radius remains in the
corresponding Riemannian ball.  This is the path-carrier step used by the
local distance-support construction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareMT.RicciFlowAnalysis

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

end PoincareMT.RicciFlowAnalysis
