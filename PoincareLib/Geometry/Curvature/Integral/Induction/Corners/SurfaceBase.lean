import PoincareLib.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareLib.Geometry.Curvature.Integral.Induction.Surface

/-!
# Two-dimensional base of the normalized corner induction

Every actual compact connected fiber surface satisfies the weighted estimate,
uniformly over ambient dimension, defining pairs and normalization parameters.
-/

open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A universal weighted estimate for every actual compact connected fiber surface. -/
theorem PoincareMT.normalizedCornerScalarBound_surface
    {n k : ℕ} (hdim : n = 2+k) (M : Type*)
    [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (δ H η : ℝ) :
    PoincareMT.NormalizedCornerScalarBound n 2 k hdim M δ H η (8*Real.pi+2) := by
  intro g D _ _ f h hf _ U _ _ _ _ _ F hF hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2+k) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
  let := openFiberChartedSpace (m := 2) hF U hreg c
  let := isManifold_openFiber (m := 2) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL : PoincareMT.RiemannianMetric 2 L :=
    PoincareMT.RiemannianMetric.Induced.pullbackMetric g incl
      (contMDiff_openFiberIncl (m := 2) hF U hreg c)
      (injective_mfderiv_openFiberIncl (m := 2) hF U hreg c)
  dsimp only
  intro hcompact hconnected _ _ _ K hK hKnonneg hKsec
  let : CompactSpace L := hcompact
  let : ConnectedSpace L := hconnected
  have hb := gL.leviCivitaData.integral_pos_scalarCurvature_surface_le hK hKnonneg hKsec
  have hI : 0 ≤ ∫ x, K x ∂gL.volumeMeasure := integral_nonneg hKnonneg
  nlinarith [mul_nonneg Real.pi_pos.le hI]


/-- The surface constant is uniform in codimension, carrier and all corner parameters. -/
theorem PoincareMT.exists_uniform_normalizedCornerScalarBound_surface :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (hdim : n = 2+k) (M : Type u)
        [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M],
        ∀ δ H η : ℝ, PoincareMT.NormalizedCornerScalarBound n 2 k hdim M δ H η C := by
  refine ⟨8*Real.pi+2, by positivity, ?_⟩
  intro n k hdim M _ _ _ _ _ _ δ H η
  exact PoincareMT.normalizedCornerScalarBound_surface hdim M δ H η


