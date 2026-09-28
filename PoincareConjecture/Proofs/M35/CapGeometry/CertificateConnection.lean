import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.Ch01.ScalarOperators










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



noncomputable def EpsilonNeck.withConnection (N : EpsilonNeck g)
    (D : LeviCivitaData g) : EpsilonNeck g :=
  { N with
    connection := D
    scalar_center_pos := by
      rw [← N.connection.scalarCurvature_eq D]
      exact N.scalar_center_pos
    scale_eq_scalar := N.scale_eq_scalar.trans
      (congrArg (fun r : ℝ => r ^ (-1 / 2 : ℝ))
        (N.connection.scalarCurvature_eq D N.center)) }

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]




noncomputable def CapCertificate.withConnection (N : CapCertificate g)
    (D : LeviCivitaData g) : CapCertificate g := by
  have hR : D.scalarCurvature = N.connection.scalarCurvature :=
    funext (D.scalarCurvature_eq N.connection)
  have hsup (U : Set M) : scalarCurvatureSupOn g D U =
      scalarCurvatureSupOn g N.connection U := by
    unfold scalarCurvatureSupOn
    rw [hR]
  have hgrad (x : M) : scalarGradientNorm g D x =
      scalarGradientNorm g N.connection x := by
    unfold scalarGradientNorm
    rw [hR]
  refine { N with
    connection := D
    end_neck := N.end_neck.withConnection D
    end_neck_connection := rfl
    boundary_neck := N.boundary_neck.withConnection D
    boundary_neck_connection := rfl
    scalar_pos := ?_
    intrinsic_diameter_bound := ?_
    scalar_ratio := ?_
    volume_bound := ?_
    core_radius_eq := ?_
    gradient_bound := ?_
    laplacian_bound := ?_ }
  · simpa only [hR] using N.scalar_pos
  · simpa only [hsup] using N.intrinsic_diameter_bound
  · simpa only [hR] using N.scalar_ratio
  · simpa only [hsup] using N.volume_bound
  · simpa only [hsup] using N.core_radius_eq
  · simpa only [hgrad, hR] using N.gradient_bound
  · obtain ⟨B, hB, hbound⟩ := N.laplacian_bound
    refine ⟨B, hB, ?_⟩
    intro x hx
    rw [hR, D.laplacian_eq N.connection, D.ricciNormSq_eq N.connection]
    exact hbound x hx



theorem CapCertificate.exists_of_metric_eq (N : CapCertificate g)
    {h : RiemannianMetric 3 M} (heq : g = h) (D : LeviCivitaData h) :
    ∃ C : CapCertificate h, C.epsilon = N.epsilon ∧
      C.cap_constant = N.cap_constant ∧ C.connection = D ∧
      C.carrier = N.carrier ∧ C.core = N.core ∧ C.closed_core = N.closed_core ∧
      C.boundary_sphere = N.boundary_sphere ∧ C.model_kind = N.model_kind := by
  subst h
  exact ⟨N.withConnection D, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture
