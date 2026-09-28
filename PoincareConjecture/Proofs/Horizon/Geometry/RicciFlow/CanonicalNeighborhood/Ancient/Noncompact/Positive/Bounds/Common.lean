import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Diameter












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



structure RegionBounds {K : AncientKappaSolution 3 M}
    {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
    (G : SoulNeckRegion K S epsilon D R) (C : ℝ) : Prop where
  scalar_pos : ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
    0 < (K.flow.connection 0).scalarCurvature x
  intrinsic_diameter_bound :
    intrinsicDiameter (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
      ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
        (G.inside ∪ G.neck.terminal_neck.carrier) ^ (-1 / 2 : ℝ))
  scalar_ratio : ∃ B : ℝ, B < C ∧
    ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
    ∀ y ∈ G.inside ∪ G.neck.terminal_neck.carrier,
      (K.flow.connection 0).scalarCurvature y ≤ B * (K.flow.connection 0).scalarCurvature x
  volume_bound :
    calibratedMetricVolume (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
      ENNReal.ofReal C * ENNReal.ofReal
        (scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
          (G.inside ∪ G.neck.terminal_neck.carrier) ^ (-3 / 2 : ℝ))
  core_ball_fields : ∃ (radius : M → ℝ) (kappa : ℝ), C⁻¹ < kappa ∧
    ∀ p ∈ interior (G.inside \ G.neck.terminal_neck.carrier),
      0 < radius p ∧
      scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
        ((K.flow.metric 0).ball p (radius p)) = (radius p)⁻¹ ^ 2 ∧
      closure ((K.flow.metric 0).ball p (radius p)) ⊆
        G.inside ∪ G.neck.terminal_neck.carrier ∧
      IsCompact (closure ((K.flow.metric 0).ball p (radius p))) ∧
      ENNReal.ofReal (kappa * radius p ^ 3) ≤
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (radius p))
  gradient_bound : ∃ B : ℝ, B < C ∧ ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
    scalarGradientNorm (K.flow.metric 0) (K.flow.connection 0) x ≤
      B * (K.flow.connection 0).scalarCurvature x ^ (3 / 2 : ℝ)
  laplacian_bound : ∃ B : ℝ, B < C ∧ ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
    |(K.flow.connection 0).laplacian (K.flow.connection 0).scalarCurvature x +
        2 * (K.flow.connection 0).ricciNormSq x| ≤
      B * (K.flow.connection 0).scalarCurvature x ^ 2

theorem uniform_regionBounds_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ R : ℝ, 1 < R → ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ → RegionBounds G C := by
  obtain ⟨epsilon₀, Cball, kappa, hepsilon₀, hsmall, hCball, _, hstrict, hballs⟩ :=
    uniform_region_core_radius_fields_of_services P
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro R hR
  obtain ⟨Cdiam, hCdiam, hdiam⟩ :=
    uniform_region_intrinsic_diameter_bound_of_services P (zero_lt_one.trans hR)
  obtain ⟨Cratio, hCratio, hratio⟩ := uniform_region_scalar_ratio_of_services P (zero_lt_one.trans hR)
  obtain ⟨Cvol, hCvol, hvol⟩ := uniform_region_volume_bound_of_services P hR
  obtain ⟨Cderiv, hCderiv, hderiv⟩ := uniform_terminal_derivative_fields_of_services P
  let C := Cball + Cdiam + Cratio + Cvol + Cderiv
  have hC : 0 < C := by dsimp [C]; positivity
  have hballC : Cball ≤ C := by dsimp [C]; linarith
  have hdiamC : Cdiam ≤ C := by dsimp [C]; linarith
  have hratioC : Cratio ≤ C := by dsimp [C]; linarith
  have hvolC : Cvol ≤ C := by dsimp [C]; linarith
  have hderivC : Cderiv ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S epsilon D G hnoncompact hepsilon
  obtain ⟨B, _, hB, hfields⟩ := hderiv K
  obtain ⟨Bratio, hBratio, hrat⟩ := hratio K S G hnoncompact
  obtain ⟨radius, hradius⟩ := hballs K S G hnoncompact hepsilon
  have hpos := fun x => (hfields x).1
  have hsup : 0 ≤ scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
      (G.inside ∪ G.neck.terminal_neck.carrier) := by
    have hb := G.compact_carrier_closure.image (K.flow.connection 0).continuous_scalarCurvature
    obtain ⟨A, hA⟩ := hb.bddAbove
    exact (G.scalarSup_pos_le hpos (fun x hx => hA ⟨x, subset_closure hx, rfl⟩)).1.le
  refine {
    scalar_pos := fun x _ => hpos x
    intrinsic_diameter_bound := (hdiam K S G hnoncompact).trans_le
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdiamC (Real.rpow_nonneg hsup _)))
    scalar_ratio := ⟨Bratio, hBratio.trans_le hratioC, hrat⟩
    volume_bound := (hvol K S G hnoncompact).trans_le
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hvolC) zero_le)
    core_ball_fields := ⟨radius, kappa, (inv_anti₀ hCball hballC).trans_lt hstrict, hradius⟩
    gradient_bound := ⟨B, hB.trans_le hderivC, fun x _ => (hfields x).2.1⟩
    laplacian_bound := ⟨B, hB.trans_le hderivC, fun x _ => (hfields x).2.2⟩ }



theorem uniform_regionBounds
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ R : ℝ, 1 < R → ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ → RegionBounds G C := by
  exact uniform_regionBounds_of_services P.noncompactServices

end PoincareConjecture.NoncompactKappa.Positive
