import PoincareConjecture.Proofs.M76.Mathlib.ConvexCylinderExterior
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem isFinitePLBallPair_convex_cylinderExterior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {Q C : Set E} (hQ : IsCompact Q) (hC : IsCompact C)
    (hQcv : Convex ℝ Q) (hCcv : Convex ℝ C)
    (hQ0 : (0 : E) ∈ interior Q) (hQC : Q ⊆ interior C) (hspace : K.space = C)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : Q = {x | ∀ i, L i x ≤ 1})
    (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsFinitePLBallPair F
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {1})
      (frontier Q ×ˢ {(1 : ℝ)}) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨D, hD, hDs, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  have hproduct : D.space = C ×ˢ Icc (-1 : ℝ) 1 := by rw [hDs, hspace, hJs]
  have hzero : (0 : E × ℝ) ∈ interior (C ×ˢ Icc (-1 : ℝ) 1) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hQC (interior_subset hQ0), by norm_num, by norm_num⟩
  let J := D.frontierSubcomplex (C ×ˢ Icc (-1 : ℝ) 1)
  exact J.isFinitePLBallPair_nested_convex_cylinderExterior
      (D.frontierSubcomplex_finite _ hD) hQ hC hQcv hCcv hQ0 hQC
      (D.frontierSubcomplex_space (hC.isClosed.prod isClosed_Icc)
        (hCcv.prod (convex_Icc _ _)) ⟨0, hzero⟩ hproduct) L hL hrep hdimEF

end Geometry.SimplicialComplex
