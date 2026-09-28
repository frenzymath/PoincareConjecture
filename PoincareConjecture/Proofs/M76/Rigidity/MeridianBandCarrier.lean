import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianRim
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem exists_finite_hamiltonMeridianBand {a b : ℝ} (hab : a < b) :
    ∃ K : SimplicialComplex ℝ (V2 × ℝ),
      K.faces.Finite ∧ K.space = Q ×ˢ Icc a b := by
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_hamiltonMeridianRim
  obtain ⟨_, _, _, _, _, q, hq, _⟩ := isFinitePLBallPair_Icc hab
  obtain ⟨_, ⟨C, hC, hCI, _⟩, _⟩ := hq
  obtain ⟨K, hK, hKS, _⟩ := J.exists_finite_triangulation_prod C hJ hC
  refine ⟨K, hK, ?_⟩
  rw [hKS, hJQ, hCI]

end PoincareConjecture.M76
