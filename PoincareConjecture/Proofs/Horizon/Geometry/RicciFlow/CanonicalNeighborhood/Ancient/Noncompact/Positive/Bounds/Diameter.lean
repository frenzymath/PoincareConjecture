import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Fields
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Intrinsic











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

theorem uniform_region_intrinsic_diameter_bound_of_services
    (P : NoncompactKappaServices.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) →
        intrinsicDiameter (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
          ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            (G.inside ∪ G.neck.terminal_neck.carrier) ^ (-1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hscalar⟩ := uniform_core_scalar_bounds_of_services P (show 0 < 2 * R by positivity)
  have hApos : 0 < A := zero_lt_one.trans hA
  refine ⟨(9 * R) * A ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S epsilon D G hnoncompact
  have hpos (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  obtain ⟨hspos, hsupper⟩ := G.scalarSup_pos_le hpos (fun x hx =>
    (hscalar K S.center hnoncompact x (G.carrier_subset_ball hx)).2.le)
  have hpower := Real.rpow_le_rpow_of_nonpos hspos hsupper
    (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  have hcancel : A ^ (1 / 2 : ℝ) *
      (A * (K.flow.connection 0).scalarCurvature S.center) ^ (-1 / 2 : ℝ) =
        (K.flow.connection 0).scalarCurvature S.center ^ (-1 / 2 : ℝ) := by
    rw [Real.mul_rpow hApos.le (hpos S.center).le, ← mul_assoc, ← Real.rpow_add hApos]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hpower (Real.rpow_pos_of_pos hApos (1 / 2 : ℝ)).le
  rw [hcancel] at hm
  apply G.intrinsic_diameter_bound.trans_le
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc, soulScalar] using
    mul_le_mul_of_nonneg_left hm (show 0 ≤ 9 * R by positivity)



theorem uniform_region_intrinsic_diameter_bound
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D : ℝ} (G : SoulNeckRegion K S epsilon D R),
        ¬ IsCompact (univ : Set M) →
        intrinsicDiameter (K.flow.metric 0) (G.inside ∪ G.neck.terminal_neck.carrier) <
          ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric 0) (K.flow.connection 0)
            (G.inside ∪ G.neck.terminal_neck.carrier) ^ (-1 / 2 : ℝ)) := by
  exact uniform_region_intrinsic_diameter_bound_of_services P.noncompactServices hR

end PoincareConjecture.NoncompactKappa.Positive
