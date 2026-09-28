import PoincareConjecture.Proofs.M76.Triangulation.HamiltonFiniteAtlasAssembly
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOverlapModelTransport
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem hasSupportedPLOverlapStraightening_of_chart_handles
    (hdim : Module.finrank ℝ E = 3)
    (hhandle : ∀ J : Finset (Fin 3), HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J) :
    OpenPartialHomeomorph.HasSupportedPLOverlapStraightening (M := M) (E := E) := by
  let L : E ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    (LinearEquiv.ofFinrankEq E (Fin 3 → ℝ) (by simpa using hdim)).toContinuousLinearEquiv
      |>.toContinuousAffineEquiv
  intro s hcompat d Q hQ hQO
  apply nonempty_supportedPLOverlapCorrection_of_covered
    (fun i : s => (i : OpenPartialHomeomorph M E)) hcompat d Q hQ hQO
  intro X _ _ _ a hac hcover b hb K hK
  apply exists_covered_straightening_affine_transport L a hac hcover b hb K hK
  intro a hac hcover b hb K hK
  have hpoint (x : X) : ∃ i, x ∈ (a i).source :=
    mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  exact exists_finite_atlas_supported_straightening a hac hpoint b hb hhandle hK

theorem hasSupportedPLOverlapStraightening_of_lower_handle_cases
    (hdim : Module.finrank ℝ E = 3)
    (indexZero : HasHamiltonChartHandleStraightening (Fin 3 → ℝ) ∅)
    (indexOne : ∀ J : Finset (Fin 3), J.card = 1 →
      HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J)
    (indexTwo : ∀ J : Finset (Fin 3), J.card = 2 →
      HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J) :
    OpenPartialHomeomorph.HasSupportedPLOverlapStraightening (M := M) (E := E) :=
  hasSupportedPLOverlapStraightening_of_chart_handles hdim
    (hasHamiltonChartHandleStraightening_of_lower_indices (by simp)
      indexZero indexOne indexTwo)

end PoincareConjecture.M76
