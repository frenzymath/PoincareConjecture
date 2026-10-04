import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.Energy
import PoincareLib.Geometry.RicciFlow.MetricComparison.LocalCurvature

/-!
# Actual controlled-speed spatial paths to the seed closure

Morgan--Tian Claim 16.27, p. 393. A point in the closed source ball
lies in the doubled open ball. The existing C1 energy reparametrization
therefore gives a real source path with speed at most twice the seed
radius, without any completeness or geodesic existence assumption.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.M04
export PoincareMT.RicciFlowAnalysis (pathSpeed)
end PoincareMT.M04
namespace PoincareMT.M04
export PoincareMT.RicciFlowAnalysis (initial_half_ball_closure_subset_initial_ball)
end PoincareMT.M04
namespace PoincareMT.M04
export PoincareMT.RicciFlowAnalysis (exists_contMDiff_energy_path_sequence)
end PoincareMT.M04

namespace PoincareMT.Proofs.M46

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

/-- The actual source path has the endpoint, spatial buffer and speed
bound needed by the transported seed tail, p. 393. -/
theorem exists_seed_spatial_path (g : RiemannianMetric n M) (x : M)
    {rho : ℝ} (hrho : 0 < rho) {z : M} (hz : z ∈ closure (g.ball x rho)) :
    ∃ gamma : ℝ → M, gamma 0 = x ∧ gamma 1 = z ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma ∧
      MapsTo gamma (Icc (0 : ℝ) 1) (g.ball x (2 * rho)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, M04.pathSpeed g gamma s ≤ 2 * rho := by
  have hball := M04.initial_half_ball_closure_subset_initial_ball g x
    (by positivity : 0 < 2 * rho)
  rw [show 2 * rho / 2 = rho by ring] at hball
  have hzball : g.edist x z < ENNReal.ofReal (2 * rho) := hball hz
  have hfinite : g.edist x z ≠ ⊤ := ne_top_of_lt hzball
  obtain ⟨gamma, hend, hsource, hspeed, _, _⟩ :=
    M04.exists_contMDiff_energy_path_sequence g hfinite (ENNReal.toReal_lt_of_lt_ofReal hzball)
  exact ⟨gamma 0, (hend 0).1, (hend 0).2.1, (hend 0).2.2, hsource 0, hspeed 0⟩

end PoincareMT.Proofs.M46
