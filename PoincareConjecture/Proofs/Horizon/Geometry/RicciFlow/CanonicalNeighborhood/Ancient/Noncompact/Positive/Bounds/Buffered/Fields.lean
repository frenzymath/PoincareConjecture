import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Buffered.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Fields
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Cap.Geometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace SoulCapGeometry

variable {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {delta epsilon D R : ℝ}
  {G : SoulNeckRegion K S delta D R} (H : SoulCapGeometry G epsilon)

theorem scalarSup_pos_le
    (hpos : ∀ x : M, 0 < (K.flow.connection 0).scalarCurvature x) {A : ℝ}
    (hbound : ∀ x ∈ H.carrier, (K.flow.connection 0).scalarCurvature x ≤ A) :
    0 < scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0) H.carrier ∧
      scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0) H.carrier ≤ A := by
  have hbounded : BddAbove (range (fun x : H.carrier =>
      (K.flow.connection 0).scalarCurvature x)) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hbound x x.property
  have hcenter : G.neck.terminal_neck.center ∈ H.carrier := Or.inr
    (G.central_sphere_subset_buffered_region H.source H.source_sphere
      (neg_neg_of_pos (inv_pos.mpr H.source.epsilon_pos)) H.outer_height_pos
      G.neck.terminal_neck.center_on_central_sphere)
  refine ⟨(hpos G.neck.terminal_neck.center).trans_le
    (le_csSup hbounded ⟨⟨G.neck.terminal_neck.center, hcenter⟩, rfl⟩), ?_⟩
  apply csSup_le (s := range (fun x : H.carrier => (K.flow.connection 0).scalarCurvature x))
    ⟨_, ⟨⟨G.neck.terminal_neck.center, hcenter⟩, rfl⟩⟩
  rintro _ ⟨x, rfl⟩
  exact hbound x x.property

theorem scalarSup_pos_le_source
    (hpos : ∀ x : M, 0 < (K.flow.connection 0).scalarCurvature x) :
    0 < scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0) H.carrier ∧
      scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0) H.carrier ≤
        scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
          (G.inside ∪ G.neck.terminal_neck.carrier) := by
  have hb : BddAbove (range (fun x : (G.inside ∪ G.neck.terminal_neck.carrier : Set M) =>
      (K.flow.connection 0).scalarCurvature x)) := by
    apply ((G.compact_carrier_closure.image
      (K.flow.connection 0).continuous_scalarCurvature).bddAbove).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, subset_closure x.property, rfl⟩
  exact H.scalarSup_pos_le hpos (fun x hx => le_csSup hb ⟨⟨x, H.carrier_subset hx⟩, rfl⟩)

end SoulCapGeometry

structure BufferedRegionBounds {K : AncientKappaSolution 3 M}
    {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {delta epsilon D R : ℝ}
    {G : SoulNeckRegion K S delta D R} (H : SoulCapGeometry G epsilon) (C : ℝ) : Prop where
  scalar_pos : ∀ x ∈ H.carrier, 0 < (K.flow.connection 0).scalarCurvature x
  intrinsic_diameter_bound : intrinsicDiameter (K.flow.metric 0) H.carrier <
    ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
      H.carrier ^ (-1 / 2 : ℝ))
  scalar_ratio : ∃ B : ℝ, B < C ∧ ∀ x ∈ H.carrier, ∀ y ∈ H.carrier,
    (K.flow.connection 0).scalarCurvature y ≤ B * (K.flow.connection 0).scalarCurvature x
  volume_bound : calibratedMetricVolume (K.flow.metric 0) H.carrier <
    ENNReal.ofReal C * ENNReal.ofReal
      (scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0) H.carrier ^ (-3 / 2 : ℝ))
  core_ball_fields : ∃ (radius : M → ℝ) (kappa : ℝ), C⁻¹ < kappa ∧
    ∀ p ∈ G.inside, 0 < radius p ∧
      scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
        ((K.flow.metric 0).ball p (radius p)) = (radius p)⁻¹ ^ 2 ∧
      closure ((K.flow.metric 0).ball p (radius p)) ⊆ H.carrier ∧
      IsCompact (closure ((K.flow.metric 0).ball p (radius p))) ∧
      ENNReal.ofReal (kappa * radius p ^ 3) ≤
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (radius p))
  gradient_bound : ∃ B : ℝ, B < C ∧ ∀ x ∈ H.carrier,
    scalarGradientNorm (K.flow.metric 0) (K.flow.connection 0) x ≤
      B * (K.flow.connection 0).scalarCurvature x ^ (3 / 2 : ℝ)
  laplacian_bound : ∃ B : ℝ, B < C ∧ ∀ x ∈ H.carrier,
    |(K.flow.connection 0).laplacian (K.flow.connection 0).scalarCurvature x +
      2 * (K.flow.connection 0).ricciNormSq x| ≤
      B * (K.flow.connection 0).scalarCurvature x ^ 2

theorem uniform_buffered_core_radius_fields_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ epsilon₀ C kappa : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      0 < C ∧ 0 < kappa ∧ C⁻¹ < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {delta epsilon D R : ℝ} {G : SoulNeckRegion K S delta D R}
        (H : SoulCapGeometry G epsilon),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ →
        ∃ radius : M → ℝ, ∀ p ∈ G.inside, 0 < radius p ∧
          scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            ((K.flow.metric 0).ball p (radius p)) = (radius p)⁻¹ ^ 2 ∧
          closure ((K.flow.metric 0).ball p (radius p)) ⊆ H.carrier ∧
          IsCompact (closure ((K.flow.metric 0).ball p (radius p))) ∧
          ENNReal.ofReal (kappa * radius p ^ 3) ≤
            calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (radius p)) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hballs⟩ := exists_scalar_ball_enclosure_threshold.{u}
  obtain ⟨C, kappa, hC, hkappa, hstrict, hvolume⟩ := uniform_scalar_radius_volume_lower_of_services P
  refine ⟨epsilon₀, C, kappa, hepsilon₀, hsmall, hC, hkappa, hstrict, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S delta epsilon D R G H hnoncompact hepsilon
  have hscalar (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  let radius := scalarCoreRadius (K.flow.metric 0) (K.flow.connection 0)
    (K.complete 0 le_rfl) hscalar
  have hspec := scalarCoreRadius_spec (K.flow.metric 0) (K.flow.connection 0)
    (K.complete 0 le_rfl) hscalar
  refine ⟨radius, ?_⟩
  intro p hp
  have hfrontier : frontier G.inside = H.boundary.central_sphere :=
    G.inside_frontier.trans (H.boundary_sphere.trans H.source_sphere).symm
  obtain ⟨hsubset, hcompact⟩ := hballs (K.flow.metric 0) (K.flow.connection 0)
    (K.complete 0 le_rfl) H.boundary (H.boundary_epsilon.trans_le hepsilon)
    G.inside G.inside_open hfrontier p hp (radius p) (hspec p).1 (hspec p).2
  exact ⟨(hspec p).1, (hspec p).2,
    hsubset.trans (union_subset (fun _ hx => Or.inl hx) H.boundary_subset), hcompact,
    hvolume K hnoncompact 0 le_rfl p (radius p) (hspec p).1 (hspec p).2⟩

theorem uniform_buffered_core_radius_fields
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ C kappa : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      0 < C ∧ 0 < kappa ∧ C⁻¹ < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {delta epsilon D R : ℝ} {G : SoulNeckRegion K S delta D R}
        (H : SoulCapGeometry G epsilon),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ →
        ∃ radius : M → ℝ, ∀ p ∈ G.inside, 0 < radius p ∧
          scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            ((K.flow.metric 0).ball p (radius p)) = (radius p)⁻¹ ^ 2 ∧
          closure ((K.flow.metric 0).ball p (radius p)) ⊆ H.carrier ∧
          IsCompact (closure ((K.flow.metric 0).ball p (radius p))) ∧
          ENNReal.ofReal (kappa * radius p ^ 3) ≤
            calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (radius p)) := by
  exact uniform_buffered_core_radius_fields_of_services P.noncompactServices

theorem uniform_buffered_intrinsic_diameter_bound_of_services
    (P : NoncompactKappaServices.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {delta epsilon D : ℝ} {G : SoulNeckRegion K S delta D R}
        (H : SoulCapGeometry G epsilon), ¬ IsCompact (univ : Set M) →
        intrinsicDiameter (K.flow.metric 0) H.carrier <
          ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            H.carrier ^ (-1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hscalar⟩ := uniform_core_scalar_bounds_of_services P (show 0 < 2 * R by positivity)
  have hApos : 0 < A := zero_lt_one.trans hA
  refine ⟨(9 * R) * A ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S delta epsilon D G H hnoncompact
  have hpos (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  obtain ⟨hspos, hsupper⟩ := H.scalarSup_pos_le hpos (fun x hx =>
    (hscalar K S.center hnoncompact x (G.carrier_subset_ball (H.carrier_subset hx))).2.le)
  have hpower := Real.rpow_le_rpow_of_nonpos hspos hsupper
    (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  have hcancel : A ^ (1 / 2 : ℝ) *
      (A * (K.flow.connection 0).scalarCurvature S.center) ^ (-1 / 2 : ℝ) =
        (K.flow.connection 0).scalarCurvature S.center ^ (-1 / 2 : ℝ) := by
    rw [Real.mul_rpow hApos.le (hpos S.center).le, ← mul_assoc, ← Real.rpow_add hApos]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hpower (Real.rpow_pos_of_pos hApos (1 / 2 : ℝ)).le
  rw [hcancel] at hm
  apply (G.buffered_intrinsic_diameter_bound H.source H.source_epsilon H.source_scale
    H.source_sphere (neg_neg_of_pos (inv_pos.mpr H.source.epsilon_pos))
    H.outer_height_pos).trans_le
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc, soulScalar] using
    mul_le_mul_of_nonneg_left hm (show 0 ≤ 9 * R by positivity)

theorem uniform_buffered_intrinsic_diameter_bound
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {delta epsilon D : ℝ} {G : SoulNeckRegion K S delta D R}
        (H : SoulCapGeometry G epsilon), ¬ IsCompact (univ : Set M) →
        intrinsicDiameter (K.flow.metric 0) H.carrier <
          ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            H.carrier ^ (-1 / 2 : ℝ)) := by
  exact uniform_buffered_intrinsic_diameter_bound_of_services P.noncompactServices hR

theorem uniform_bufferedRegionBounds_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ R : ℝ, 1 < R → ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {delta epsilon D : ℝ} {G : SoulNeckRegion K S delta D R}
        (H : SoulCapGeometry G epsilon),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ → BufferedRegionBounds H C := by
  obtain ⟨epsilon₀, Cball, kappa, hepsilon₀, hsmall, hCball, _, hstrict, hballs⟩ :=
    uniform_buffered_core_radius_fields_of_services P
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro R hR
  obtain ⟨Cdiam, hCdiam, hdiam⟩ :=
    uniform_buffered_intrinsic_diameter_bound_of_services P (zero_lt_one.trans hR)
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
  intro M _ _ _ _ _ _ _ _ _ K S delta epsilon D G H hnoncompact hepsilon
  obtain ⟨B, _, hB, hfields⟩ := hderiv K
  obtain ⟨Bratio, hBratio, hrat⟩ := hratio K S G hnoncompact
  obtain ⟨radius, hradius⟩ := hballs K S H hnoncompact hepsilon
  have hpos := fun x => (hfields x).1
  obtain ⟨hsup, hsup_le⟩ := H.scalarSup_pos_le_source hpos
  have hvolume : calibratedMetricVolume (K.flow.metric 0) H.carrier <
      ENNReal.ofReal C * ENNReal.ofReal
        (scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
          H.carrier ^ (-3 / 2 : ℝ)) := by
    apply ((MeasureTheory.measure_mono H.carrier_subset).trans_lt
      (hvol K S G hnoncompact)).trans_le
    apply mul_le_mul
    · exact ENNReal.ofReal_le_ofReal hvolC
    · exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos hsup hsup_le (by norm_num))
    · exact zero_le
    · exact zero_le
  exact {
    scalar_pos := fun x _ => hpos x
    intrinsic_diameter_bound := (hdiam K S H hnoncompact).trans_le
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdiamC (Real.rpow_nonneg hsup.le _)))
    scalar_ratio := ⟨Bratio, hBratio.trans_le hratioC,
      fun x hx y hy => hrat x (H.carrier_subset hx) y (H.carrier_subset hy)⟩
    volume_bound := hvolume
    core_ball_fields := ⟨radius, kappa, (inv_anti₀ hCball hballC).trans_lt hstrict, hradius⟩
    gradient_bound := ⟨B, hB.trans_le hderivC, fun x _ => (hfields x).2.1⟩
    laplacian_bound := ⟨B, hB.trans_le hderivC, fun x _ => (hfields x).2.2⟩ }

theorem uniform_bufferedRegionBounds
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ R : ℝ, 1 < R → ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {delta epsilon D : ℝ} {G : SoulNeckRegion K S delta D R}
        (H : SoulCapGeometry G epsilon),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ → BufferedRegionBounds H C := by
  exact uniform_bufferedRegionBounds_of_services P.noncompactServices

end PoincareConjecture.NoncompactKappa.Positive
