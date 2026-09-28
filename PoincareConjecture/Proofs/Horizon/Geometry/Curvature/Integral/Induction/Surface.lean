import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.TotalCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.FiniteComponents







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

theorem PoincareConjecture.LeviCivitaData.integral_pos_scalarCurvature_surface_le
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    {g : PoincareConjecture.RiemannianMetric 2 M} (D : PoincareConjecture.LeviCivitaData g)
    {K : M → ℝ} (hKc : Continuous K) (hK : ∀ x, 0 ≤ K x)
    (hsec : ∀ x (v w : TangentSpace (𝓡 2) x),
      -K x ≤ D.sectionalCurvature x v w) :
    (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      8 * Real.pi + 2 * ∫ x, K x ∂g.volumeMeasure := by
  have hR : Integrable D.scalarCurvature g.volumeMeasure :=
    D.continuous_scalarCurvature.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hKi : Integrable K g.volumeMeasure :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP : Integrable (fun x => max 0 (D.scalarCurvature x)) g.volumeMeasure := by
    simpa only [max_comm] using hR.pos_part
  have hb := integral_mono hP (hR.add (hKi.const_mul 2)) (fun x => by
    have hs := D.scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound
      x (K x) (hsec x)
    norm_num at hs
    dsimp only [Pi.add_apply]
    exact max_le (by linarith) (by linarith [hK x]))
  simp only [Pi.add_apply] at hb
  rw [integral_add hR (hKi.const_mul 2), integral_const_mul] at hb
  exact hb.trans (add_le_add D.integral_scalarCurvature_le_eight_pi le_rfl)


theorem PoincareConjecture.LeviCivitaData.integral_pos_scalarCurvature_surface_le_components
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [CompactSpace M]
    {g : PoincareConjecture.RiemannianMetric 2 M} (D : PoincareConjecture.LeviCivitaData g)
    {K : M → ℝ} (hKc : Continuous K) (hK : ∀ x, 0 ≤ K x)
    (hsec : ∀ x (v w : TangentSpace (𝓡 2) x),
      -K x ≤ D.sectionalCurvature x v w) :
    (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      8 * Real.pi * (Nat.card (ConnectedComponents M) : ℝ) +
        2 * ∫ x, K x ∂g.volumeMeasure := by
  classical
  have hKi : Integrable K g.volumeMeasure :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb := g.integral_pos_scalarCurvature_le_of_connectedComponent_bounds
    D K hKi (show 0 ≤ 4 * Real.pi by positivity) (show (0:ℝ) ≤ 2 by norm_num)
    (Nat.card (ConnectedComponents M)) le_rfl (fun p => by
      let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 2)) p
      let gU := g.connectedComponentMetric p
      have hUc : IsCompact (U : Set M) := isClosed_connectedComponent.isCompact
      let : CompactSpace U := isCompact_iff_compactSpace.mp hUc
      have hsecU (x : U) (v w : TangentSpace (𝓡 2) x) :
          -K x ≤ gU.leviCivitaData.sectionalCurvature x v w := by
        rw [g.sectionalCurvature_connectedComponentMetric D p x v w]
        exact hsec x _ _
      have h := gU.leviCivitaData.integral_pos_scalarCurvature_surface_le
        (hKc.comp continuous_subtype_val) (fun x => hK x) hsecU
      dsimp only [Function.comp_def, gU] at h
      convert h using 1; ring)
  convert hb using 1; ring
