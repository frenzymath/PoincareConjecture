import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.SourceMeridianRim
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.AlexanderBaseProductBall

/-!
# The complete finite meridian band carrier

The original square rim and full closed interval give one finite
triangulation, retaining both endpoint rims. See rigidity037,
sections3 and5.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

/-- Triangulate the entire prescribed band, with arbitrary ordered
closed endpoints. See rigidity037, section3. -/
theorem exists_finite_hamiltonMeridianBand {a b : ℝ} (hab : a < b) :
    ∃ K : SimplicialComplex ℝ (V2 × ℝ),
      K.faces.Finite ∧ K.space = Q ×ˢ Icc a b := by
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_hamiltonMeridianRim
  obtain ⟨_, _, _, _, _, q, hq, _⟩ := isFinitePLBallPair_Icc hab
  obtain ⟨_, ⟨C, hC, hCI, _⟩, _⟩ := hq
  obtain ⟨K, hK, hKS, _⟩ := J.exists_finite_triangulation_prod C hJ hC
  refine ⟨K, hK, ?_⟩
  rw [hKS, hJQ, hCI]

end PoincareMT.M76
