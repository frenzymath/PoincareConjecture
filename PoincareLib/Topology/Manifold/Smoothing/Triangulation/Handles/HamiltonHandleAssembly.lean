import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonFiniteAtlasAssembly
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonOverlapModelTransport
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonAlexanderConsequences

/-!
# The actual finite overlap assembly from Hamilton's handle cases

The finite simplex construction runs on the literal overlap. A fixed
affine coordinate change transfers the result to any three-dimensional
model. Alexander discharges index three, leaving exactly the three lower
handle cases. See Hamilton 1976, pp. 64--69 and M76 derivation 330.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The four coordinate handle cases produce every field of the literal
supported overlap correction. No finite handle decomposition, relative
collar, or assembly supplier is assumed. See Hamilton p.69 and derivation330. -/
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

/-- Supported overlap straightening now requires exactly Hamilton's
three lower chart-handle cases. The Alexander case and the complete
finite relative handle assembly are proved. See Hamilton pp.64--69 and
M76 derivations330 and333. -/
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

end PoincareMT.M76
