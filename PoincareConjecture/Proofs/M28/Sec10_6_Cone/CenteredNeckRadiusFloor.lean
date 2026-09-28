import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckCompletionRadius
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedSphereRayCrossing
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RecutArbitraryNeckContainment











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}





theorem centered_neck_scalar_radius_floor
    (N : EpsilonNeck g) (D : LeviCivitaData g)
    (U : TopologicalSpace.Opens M) (hNU : N.carrier ⊆ (U : Set M))
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      ∀ x : U, N.center = (x : M) →
        (1 / 16 : ℝ) < D.scalarCurvature x *
          dist (x : UniformSpace.Completion U) E ^ 2 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside x hcenter
  have hx : (x : M) ∈ N.central_sphere := hcenter ▸ N.center_on_central_sphere
  have hr := (neck_completion_radius_lower N U hNU hfinite E houtside x hx).2
  have hnormal := tube.neck_normalized_scalar_center N D
  rw [hcenter] at hnormal
  have hQ : 0 < D.scalarCurvature x := by
    have hsquare := sq_pos_of_pos N.scale_pos
    nlinarith only [hnormal, hsquare]
  have hradius : 0 < dist (x : UniformSpace.Completion U) E :=
    (div_pos N.scale_pos (by norm_num : (0 : ℝ) < 4)).trans hr
  have hsq : (N.scale / 4) ^ 2 < dist (x : UniformSpace.Completion U) E ^ 2 := by
    have hscale := N.scale_pos
    nlinarith only [hr, hscale, hradius]
  have hmul := mul_lt_mul_of_pos_left hsq hQ
  nlinarith only [hmul, hnormal]

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in




theorem exists_centered_neck_radius_floor_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (X : Set M)
        (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
        (U : TopologicalSpace.Opens M),
        (U : Set M) = A.tail true (1 / 2) → IsCompact (frontier (U : Set M)) →
        ∀ K : NeckOnlyCover g, (U : Set M) ⊆ K.X → K.epsilon ≤ epsilon0 →
        (∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
          ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x) →
        ∀ hfinite : ∀ p q : U,
          intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤,
        letI := intrinsicOpenMetricSpace g U hfinite
        ∀ E : UniformSpace.Completion U,
          E ∉ range ((↑) : U → UniformSpace.Completion U) →
          ∃ eta : ℝ, 0 < eta ∧ ∀ x : U,
            (3 / 4 : ℝ) ≤ (A.inverse x).2 →
            dist (x : UniformSpace.Completion U) E < eta →
              (1 / 16 : ℝ) < D.scalarCurvature x *
                dist (x : UniformSpace.Completion U) E ^ 2 := by
  obtain ⟨epsilon0, hpos, hsmall, hexclude⟩ := exists_neck_frontier_exclusion_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D X T A U hU hfront K hUK hK hdiverge hfinite
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  obtain ⟨B, hB⟩ := hexclude M g D (U : Set M) U.isOpen hfront
  obtain ⟨d, _hdhalf, hd1, hhigh⟩ := hdiverge B
  obtain ⟨eta, heta, hheight⟩ :=
    exists_completion_radius_threshold_for_cylinder_height T A U hU hfinite E houtside d hd1
  refine ⟨eta, heta, ?_⟩
  intro x hlower hradius
  have hRhigh := hhigh x (hUV x.property) (hheight x hlower hradius)
  obtain ⟨N, hN, hcenter⟩ := K.pointwise_center_cover x (hUK x.property)
  have hNsmall : N.epsilon ≤ epsilon0 := (K.neck_epsilon N hN).trans_le hK
  have hNU : N.carrier ⊆ (U : Set M) :=
    hB N hNsmall (hcenter.symm ▸ x.property) (hcenter.symm ▸ hRhigh)
  exact centered_neck_scalar_radius_floor N D U hNU hfinite E houtside x hcenter

end PoincareConjecture.M28
