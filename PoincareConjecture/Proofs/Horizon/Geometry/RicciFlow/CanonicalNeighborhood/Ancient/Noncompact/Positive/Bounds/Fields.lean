import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.CoreBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.VolumeScaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Main













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

theorem SoulNeckRegion.scalarSup_pos_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {K : AncientKappaSolution 3 M} {S : RiemannianMetric.PointSoulData (K.flow.metric 0)}
    {epsilon D R : ℝ} (G : SoulNeckRegion K S epsilon D R)
    (hpos : ∀ x : M, 0 < (K.flow.connection 0).scalarCurvature x) {A : ℝ}
    (hbound : ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
      (K.flow.connection 0).scalarCurvature x ≤ A) :
    0 < scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
        (G.inside ∪ G.neck.terminal_neck.carrier) ∧
      scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
        (G.inside ∪ G.neck.terminal_neck.carrier) ≤ A := by
  let U := G.inside ∪ G.neck.terminal_neck.carrier
  have hbounded : BddAbove (range (fun x : U => (K.flow.connection 0).scalarCurvature x)) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hbound x x.property
  have hxU : G.neck.terminal_neck.center ∈ U :=
    Or.inr (G.neck.terminal_neck.central_sphere_subset G.neck.terminal_neck.center_on_central_sphere)
  refine ⟨(hpos G.neck.terminal_neck.center).trans_le
    (le_csSup hbounded ⟨⟨G.neck.terminal_neck.center, hxU⟩, rfl⟩), ?_⟩
  apply csSup_le (s := range (fun x : U => (K.flow.connection 0).scalarCurvature x))
    ⟨_, ⟨⟨G.neck.terminal_neck.center, hxU⟩, rfl⟩⟩
  rintro _ ⟨x, rfl⟩
  exact hbound x x.property



theorem uniform_terminal_derivative_fields_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ x : M,
          0 < (K.flow.connection 0).scalarCurvature x ∧
          scalarGradientNorm (K.flow.metric 0) (K.flow.connection 0) x ≤
            B * (K.flow.connection 0).scalarCurvature x ^ (3 / 2 : ℝ) ∧
          |(K.flow.connection 0).laplacian (K.flow.connection 0).scalarCurvature x +
              2 * (K.flow.connection 0).ricciNormSq x| ≤
            B * (K.flow.connection 0).scalarCurvature x ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := uniformKappaScalarDerivativeBounds_of_services P.toScalarDerivativeServices
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K
  obtain ⟨B, hB, hBC, hfields⟩ := hbound K
  refine ⟨B, hB, hBC, ?_⟩
  intro x
  obtain ⟨hpos, hgrad, d, hd, htime⟩ := hfields 0 le_rfl x
  refine ⟨hpos, hgrad, ?_⟩
  have heq := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv (Iic 0) hd
    (P.scalar_evolution M (Iic 0) K.flow 0 (by simp) x)
  rwa [heq] at htime



theorem uniform_terminal_derivative_fields
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ x : M,
          0 < (K.flow.connection 0).scalarCurvature x ∧
          scalarGradientNorm (K.flow.metric 0) (K.flow.connection 0) x ≤
            B * (K.flow.connection 0).scalarCurvature x ^ (3 / 2 : ℝ) ∧
          |(K.flow.connection 0).laplacian (K.flow.connection 0).scalarCurvature x +
              2 * (K.flow.connection 0).ricciNormSq x| ≤
            B * (K.flow.connection 0).scalarCurvature x ^ 2 := by
  exact uniform_terminal_derivative_fields_of_services P.noncompactServices



theorem uniform_region_core_radius_fields_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ epsilon₀ C kappa : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      0 < C ∧ 0 < kappa ∧ C⁻¹ < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D R : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ →
        ∃ radius : M → ℝ, ∀ p ∈ interior (G.inside \ G.neck.terminal_neck.carrier),
          0 < radius p ∧
          scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            ((K.flow.metric 0).ball p (radius p)) = (radius p)⁻¹ ^ 2 ∧
          closure ((K.flow.metric 0).ball p (radius p)) ⊆
            G.inside ∪ G.neck.terminal_neck.carrier ∧
          IsCompact (closure ((K.flow.metric 0).ball p (radius p))) ∧
          ENNReal.ofReal (kappa * radius p ^ 3) ≤
            calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (radius p)) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hballs⟩ := exists_scalar_ball_enclosure_threshold.{u}
  obtain ⟨C, kappa, hC, hkappa, hstrict, hvolume⟩ := uniform_scalar_radius_volume_lower_of_services P
  refine ⟨epsilon₀, C, kappa, hepsilon₀, hsmall, hC, hkappa, hstrict, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S epsilon D R G hnoncompact hepsilon
  have hscalar (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  let radius := scalarCoreRadius (K.flow.metric 0) (K.flow.connection 0)
    (K.complete 0 le_rfl) hscalar
  have hspec := scalarCoreRadius_spec (K.flow.metric 0) (K.flow.connection 0)
    (K.complete 0 le_rfl) hscalar
  refine ⟨radius, ?_⟩
  intro p hp
  have hpA := (interior_subset hp).1
  obtain ⟨hsubset, hcompact⟩ := hballs (K.flow.metric 0) (K.flow.connection 0)
    (K.complete 0 le_rfl) G.neck.terminal_neck
    (G.neck.terminal_epsilon.trans_le hepsilon) G.inside G.inside_open
    G.inside_frontier p hpA (radius p) (hspec p).1 (hspec p).2
  exact ⟨(hspec p).1, (hspec p).2, hsubset, hcompact,
    hvolume K hnoncompact 0 le_rfl p (radius p) (hspec p).1 (hspec p).2⟩



theorem uniform_region_core_radius_fields
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ C kappa : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      0 < C ∧ 0 < kappa ∧ C⁻¹ < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D R : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) → epsilon ≤ epsilon₀ →
        ∃ radius : M → ℝ, ∀ p ∈ interior (G.inside \ G.neck.terminal_neck.carrier),
          0 < radius p ∧
          scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            ((K.flow.metric 0).ball p (radius p)) = (radius p)⁻¹ ^ 2 ∧
          closure ((K.flow.metric 0).ball p (radius p)) ⊆
            G.inside ∪ G.neck.terminal_neck.carrier ∧
          IsCompact (closure ((K.flow.metric 0).ball p (radius p))) ∧
          ENNReal.ofReal (kappa * radius p ^ 3) ≤
            calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p (radius p)) := by
  exact uniform_region_core_radius_fields_of_services P.noncompactServices



theorem uniform_region_scalar_ratio_of_services
    (P : NoncompactKappaServices.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) →
        ∃ B : ℝ, B < C ∧
          ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
          ∀ y ∈ G.inside ∪ G.neck.terminal_neck.carrier,
            (K.flow.connection 0).scalarCurvature y ≤
              B * (K.flow.connection 0).scalarCurvature x := by
  obtain ⟨A, hA, hbound⟩ := uniform_core_scalar_bounds_of_services P (show 0 < 2 * R by positivity)
  have hApos : 0 < A := zero_lt_one.trans hA
  refine ⟨A ^ 2 + 1, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S epsilon D G hnoncompact
  refine ⟨A ^ 2, by linarith, ?_⟩
  intro x hx y hy
  have hlow := (hbound K S.center hnoncompact x (G.carrier_subset_ball hx)).1
  have hupp := (hbound K S.center hnoncompact y (G.carrier_subset_ball hy)).2
  have hreverse : (K.flow.connection 0).scalarCurvature S.center <
      A * (K.flow.connection 0).scalarCurvature x := by
    have hm := mul_lt_mul_of_pos_left hlow hApos
    simpa only [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul] using hm
  have hm := mul_lt_mul_of_pos_left hreverse hApos
  nlinarith



theorem uniform_region_scalar_ratio
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) →
        ∃ B : ℝ, B < C ∧
          ∀ x ∈ G.inside ∪ G.neck.terminal_neck.carrier,
          ∀ y ∈ G.inside ∪ G.neck.terminal_neck.carrier,
            (K.flow.connection 0).scalarCurvature y ≤
              B * (K.flow.connection 0).scalarCurvature x := by
  exact uniform_region_scalar_ratio_of_services P.noncompactServices hR



theorem uniform_region_volume_bound_of_services
    (P : NoncompactKappaServices.{u}) {R : ℝ} (hR : 1 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) →
        calibratedMetricVolume (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
          ENNReal.ofReal C * ENNReal.ofReal
            (scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
              (G.inside ∪ G.neck.terminal_neck.carrier) ^ (-3 / 2 : ℝ)) := by
  obtain ⟨A, hA, hscalar⟩ := uniform_core_scalar_bounds_of_services P (show 0 < 2 * R by linarith)
  obtain ⟨v, V, _, hV, hvolume⟩ :=
    noncompact_core_uniform_scaled_volume_bounds_of_services P (show 1 < 2 * R by linarith)
  have hApos : 0 < A := zero_lt_one.trans hA
  refine ⟨V * A ^ (3 / 2 : ℝ), mul_pos hV (Real.rpow_pos_of_pos hApos _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S epsilon D G hnoncompact
  let U := G.inside ∪ G.neck.terminal_neck.carrier
  let s := scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0) U
  have hpos (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  obtain ⟨hspos, hsupper⟩ := G.scalarSup_pos_le hpos (fun x hx =>
    (hscalar K S.center hnoncompact x (G.carrier_subset_ball hx)).2.le)
  have hpower := Real.rpow_le_rpow_of_nonpos hspos hsupper
    (show (-3 / 2 : ℝ) ≤ 0 by norm_num)
  have hcancel : A ^ (3 / 2 : ℝ) *
      (A * (K.flow.connection 0).scalarCurvature S.center) ^ (-3 / 2 : ℝ) =
        (K.flow.connection 0).scalarCurvature S.center ^ (-3 / 2 : ℝ) := by
    rw [Real.mul_rpow hApos.le (hpos S.center).le, ← mul_assoc, ← Real.rpow_add hApos]
    norm_num
  have hcomparison : V * (K.flow.connection 0).scalarCurvature S.center ^ (-3 / 2 : ℝ) ≤
      (V * A ^ (3 / 2 : ℝ)) * s ^ (-3 / 2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hpower (Real.rpow_pos_of_pos hApos (3 / 2 : ℝ)).le
    rw [hcancel] at hm
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm hV.le
  have hvol := (hvolume K S.center (K.not_isRound_of_noncompact hnoncompact)).2
  apply ((MeasureTheory.measure_mono G.carrier_subset_ball).trans_lt hvol).trans_le
  rw [← ENNReal.ofReal_mul (mul_pos hV (Real.rpow_pos_of_pos hApos _)).le]
  exact ENNReal.ofReal_le_ofReal hcomparison



theorem uniform_region_volume_bound
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {R : ℝ} (hR : 1 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) →
        calibratedMetricVolume (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
          ENNReal.ofReal C * ENNReal.ofReal
            (scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
              (G.inside ∪ G.neck.terminal_neck.carrier) ^ (-3 / 2 : ℝ)) := by
  exact uniform_region_volume_bound_of_services P.noncompactServices hR

end PoincareConjecture.NoncompactKappa.Positive
