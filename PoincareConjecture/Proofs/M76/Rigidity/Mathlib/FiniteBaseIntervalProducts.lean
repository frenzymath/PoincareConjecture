import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finite_interval_product (L : SimplicialComplex ℝ E)
    (hL : L.faces.Finite) {a b : ℝ} (hab : a < b) :
    ∃ K : SimplicialComplex ℝ (E × ℝ),
      K.faces.Finite ∧ K.space = L.space ×ˢ Icc a b := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc hab
  obtain ⟨K, hK, hKs, _⟩ := L.exists_finite_triangulation_prod J hL hJ
  exact ⟨K, hK, hKs.trans (congrArg (fun t => L.space ×ˢ t) hJI)⟩

end Geometry.SimplicialComplex
