import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature
import PoincareLib.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities

/-!
# The compact factor of a normalized limiting potential

Any unit parallel potential on a complete three-manifold of scalar curvature
one has a complete zero level of scalar curvature one. In dimension two this
is a positive Ricci lower bound, so Bonnet--Myers makes that same level compact.
This applies directly to a limit of the normalized source potentials.

Reference: Morgan--Tian, Proposition 9.46, pp. 209-213.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {f : M → ℝ}

/-- The actual zero level of any unit parallel potential in a complete
unit-scalar three-manifold is compact, connected, and has scalar curvature one. -/
theorem compact_unitScalar_zeroLevel_of_parallel
    (hc : MetricComplete g) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    (hR : ∀ x, D.scalarCurvature x = 1) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 2 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 2 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧
      CompactSpace (zeroLevelSet f) ∧ MetricComplete h ∧
      ∀ y, h.leviCivitaData.scalarCurvature y = 1 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg 2 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  obtain ⟨hne, hconn, hcomplete, _⟩ := exists_parallelGradient_productIsometry hc hf hu hz
  let : ConnectedSpace (zeroLevelSet f) := hconn
  have hscalar (y : zeroLevelSet f) : h.leviCivitaData.scalarCurvature y = 1 :=
    (parallelGradient_factor_curvature hf hu hz y).2.2.2.1.trans (hR _)
  have hcompact : CompactSpace (zeroLevelSet f) :=
    h.compactSpace_of_positive_ricci h.leviCivitaData hcomplete
      (by norm_num : (0 : ℝ) < 1 / 2) (fun y v => by
        rw [h.leviCivitaData.ricci_eq_half_scalarCurvature_mul_inner, hscalar])
  exact ⟨hne, hconn, hcompact, hcomplete, hscalar⟩

end PoincareMT.RiemannianMetric
