import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Step
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ModelReduction
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ScalarConsumer
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Monotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.SurfaceBase
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Small
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AmbientReduction

open Set Function TopologicalSpace MeasureTheory
open PoincareConjecture
open scoped Manifold ContDiff Bundle
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def UniformNormalizedCornerBounds (d k : ℕ) (δ : ℝ) : Prop :=
  ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
    ∀ (M : Type) [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin (d+k))) M] [IsManifold (𝓡 (d+k)) ∞ M],
      PoincareConjecture.NormalizedCornerScalarBound (d+k) d k rfl M δ H η C

private theorem uniform_normalized_bounds_of_dimension
    (n d k : ℕ) (hdim : n=d+k) (δ : ℝ) (h : UniformNormalizedCornerBounds d k δ) :
    ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type) [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M],
        PoincareConjecture.NormalizedCornerScalarBound n d k hdim M δ H η C := by
  subst n
  exact h

private theorem normalized_dimension_induction :
    ∀ j k : ℕ, ∃ δ : ℝ, 0 < δ ∧ UniformNormalizedCornerBounds (j+2) k δ := by
  intro j
  induction j with
  | zero =>
    intro k
    refine ⟨1, zero_lt_one, ?_⟩
    intro H _ η _
    refine ⟨8*Real.pi+2, by positivity, ?_⟩
    intro M _ _ _ _ _ _
    exact PoincareConjecture.normalizedCornerScalarBound_surface rfl M 1 H η
  | succ j ih =>
    intro k
    obtain ⟨δ, hδ, hfamily⟩ := ih (k+1)
    let Δ := min δ (min (1/(16*((k:ℝ)+1))) (1/(256*((k:ℝ)+2)^2)))
    have hΔ : 0 < Δ := by dsimp only [Δ]; positivity
    have hΔδ : Δ ≤ δ := min_le_left _ _
    have hΔ₁ : Δ ≤ 1/(16*((k:ℝ)+1)) := (min_le_right _ _).trans (min_le_left _ _)
    have hΔ₂ : Δ ≤ 1/(256*((k:ℝ)+2)^2) := (min_le_right _ _).trans (min_le_right _ _)
    have hfamily' : UniformNormalizedCornerBounds ((j+1)+1) (k+1) Δ := by
      intro H hH η hη
      obtain ⟨C,hC,hCbound⟩ := hfamily H hH η hη
      refine ⟨C,hC,?_⟩
      intro M _ _ _ _ _ _
      exact (hCbound M).mono hΔδ le_rfl le_rfl le_rfl
    obtain ⟨δ₀,hδ₀,hmodel⟩ :=
      PoincareConjecture.exists_uniform_pointedCornerModel_scalar_bound_of_lower_dimensional_bound
        (j+1) k (by omega) Δ hΔ hΔ₁ hΔ₂
        (uniform_normalized_bounds_of_dimension _ _ _ (by omega) Δ hfamily')
    refine ⟨δ₀,hδ₀,?_⟩
    intro H hH η hη
    obtain ⟨C,hC,hsmall⟩ :=
      PoincareConjecture.exists_normalizedCornerScalarBound_of_pointedCornerModel_bound
        ((j+1)+2) k (by omega) δ₀ H η hH hη (by
          obtain ⟨B, _, hB⟩ := hmodel H hH
          exact ⟨B,hB⟩)
    refine ⟨C,hC,?_⟩
    intro M _ _ _ _ _ _
    exact PoincareConjecture.normalizedCornerScalarBound_of_connected_ambient
      (((j+1)+2)+k) ((j+1)+2) k rfl δ₀ H η C hsmall M

theorem PoincareConjecture.exists_uniform_normalizedCornerScalarBound
    (m k : ℕ) (hm : 2 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ (M : Type u)
        [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
        [IsManifold (𝓡 (m+k)) ∞ M],
        NormalizedCornerScalarBound (m+k) m k rfl M δ H η C := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m=j+2 := ⟨m-2, by omega⟩
  obtain ⟨δ,hδ,hfamily⟩ := normalized_dimension_induction j k
  refine ⟨δ,hδ,?_⟩
  intro H hH η hη
  obtain ⟨C,hC,hsmall⟩ := hfamily H hH η hη
  have hlarge : ∀ (N : Type u) [TopologicalSpace N] [T3Space N] [PreconnectedSpace N]
      [MeasurableSpace N] [BorelSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin ((j+2)+k))) N]
      [IsManifold (𝓡 ((j+2)+k)) ∞ N],
      NormalizedCornerScalarBound ((j+2)+k) (j+2) k rfl N δ H η C :=
    PoincareConjecture.normalizedCornerScalarBound_of_small rfl δ H η C
      (fun N _ _ _ _ _ _ _ => hsmall N)
  refine ⟨C,hC,?_⟩
  intro M _ _ _ _ _ _
  exact PoincareConjecture.normalizedCornerScalarBound_of_connected_ambient
    ((j+2)+k) (j+2) k rfl δ H η C (fun N _ _ _ _ _ _ _ => hlarge N) M

theorem PoincareConjecture.exists_uniform_pointedCornerModel_scalar_bound
    (m k : ℕ) (hm : 3 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : ℝ, 0 ≤ H →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : PointedCornerModel m k δ H, A.weightedRatio ≤ B := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m=j+3 := ⟨m-3, by omega⟩
  obtain ⟨δ,hδ,hfamily⟩ := normalized_dimension_induction j (k+1)
  let Δ := min δ (min (1/(16*((k:ℝ)+1))) (1/(256*((k:ℝ)+2)^2)))
  have hΔ : 0 < Δ := by dsimp only [Δ]; positivity
  have hΔδ : Δ ≤ δ := min_le_left _ _
  have hΔ₁ : Δ ≤ 1/(16*((k:ℝ)+1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hΔ₂ : Δ ≤ 1/(256*((k:ℝ)+2)^2) := (min_le_right _ _).trans (min_le_right _ _)
  have hfamily' : UniformNormalizedCornerBounds ((j+1)+1) (k+1) Δ := by
    intro H hH η hη
    obtain ⟨C,hC,hCbound⟩ := hfamily H hH η hη
    refine ⟨C,hC,?_⟩
    intro M _ _ _ _ _ _
    exact (hCbound M).mono hΔδ le_rfl le_rfl le_rfl
  exact PoincareConjecture.exists_uniform_pointedCornerModel_scalar_bound_of_lower_dimensional_bound
    (j+1) k (by omega) Δ hΔ hΔ₁ hΔ₂
    (uniform_normalized_bounds_of_dimension _ _ _ (by omega) Δ hfamily')

theorem PoincareConjecture.exists_uniform_unitBall_scalar_integral_bound_of_three_le
    (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M, (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  obtain ⟨δ,_,hmodel⟩ :=
    PoincareConjecture.exists_uniform_pointedCornerModel_scalar_bound n 0 hn
  obtain ⟨B,_,hB⟩ := hmodel 0 le_rfl
  exact PoincareConjecture.exists_uniform_unitBall_scalar_integral_bound_of_corner_models
    n (by omega) δ ⟨B,hB⟩
