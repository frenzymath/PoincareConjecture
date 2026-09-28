import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Surface

open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.normalizedCornerScalarBound_surface
    {n k : ℕ} (hdim : n = 2+k) (M : Type*)
    [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (δ H η : ℝ) :
    PoincareConjecture.NormalizedCornerScalarBound n 2 k hdim M δ H η (8*Real.pi+2) := by
  intro g D _ _ f h hf _ U _ _ _ _ _ F hF hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2+k) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
  let := openFiberChartedSpace (m := 2) hF U hreg c
  let := isManifold_openFiber (m := 2) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL : PoincareConjecture.RiemannianMetric 2 L :=
    PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g incl
      (contMDiff_openFiberIncl (m := 2) hF U hreg c)
      (injective_mfderiv_openFiberIncl (m := 2) hF U hreg c)
  dsimp only
  intro hcompact hconnected _ _ _ K hK hKnonneg hKsec
  let : CompactSpace L := hcompact
  let : ConnectedSpace L := hconnected
  have hb := gL.leviCivitaData.integral_pos_scalarCurvature_surface_le hK hKnonneg hKsec
  have hI : 0 ≤ ∫ x, K x ∂gL.volumeMeasure := integral_nonneg hKnonneg
  nlinarith [mul_nonneg Real.pi_pos.le hI]

theorem PoincareConjecture.exists_uniform_normalizedCornerScalarBound_surface :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (hdim : n = 2+k) (M : Type u)
        [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M],
        ∀ δ H η : ℝ, PoincareConjecture.NormalizedCornerScalarBound n 2 k hdim M δ H η C := by
  refine ⟨8*Real.pi+2, by positivity, ?_⟩
  intro n k hdim M _ _ _ _ _ _ δ H η
  exact PoincareConjecture.normalizedCornerScalarBound_surface hdim M δ H η
