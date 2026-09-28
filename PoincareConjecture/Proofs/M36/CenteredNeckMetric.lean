import PoincareConjecture.Proofs.M36.CenteredNeckChart
import PoincareConjecture.Proofs.M36.NeckMetricBound
import PoincareConjecture.Proofs.M01.NormalizationMetric
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

noncomputable def normalizedNeckMetric (N : EpsilonNeck g) : RiemannianMetric 3 M :=
  m01RescaledMetric g (N.connection.scalarCurvature N.center) N.scalar_center_pos

noncomputable def normalizedNeckConnection (N : EpsilonNeck g) :
    LeviCivitaData (normalizedNeckMetric N) :=
  m01RescaledMetric_connection g N.connection
    (N.connection.scalarCurvature N.center) N.scalar_center_pos

theorem centeredNeckLift_mfderiv (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ)
    {p : E₃} (hp : p ∈ centeredNeckDomain N s) (v : E₃) :
    mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p v =
      mfderiv IC (𝓡 3) N.coordinate_map (centeredCylinderLift theta s p)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) theta).symm
          (cylinderHorizontalProjection p) (cylinderHorizontalProjection v),
          cylinderHeightCovector v) := by
  have hN := (neck_coordinate_contMDiffAt N (z := centeredCylinderLift theta s p)
    ⟨Set.mem_univ _, hp⟩).mdifferentiableAt (by simp)
  have hA := (centeredCylinderLift_contMDiff theta s p).mdifferentiableAt (by simp)
  have hd := congrArg (fun D => D v) (mfderiv_comp p hN hA)
  change mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p v =
    mfderiv IC (𝓡 3) N.coordinate_map (centeredCylinderLift theta s p)
      (mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p v) at hd
  rw [centeredCylinderLift_mfderiv] at hd
  exact hd

theorem normalizedNeckMetric_pullbackCoefficients (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    (normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N theta s) p =
      centeredCylinderMetric (fun z v w => normalizedNeckForm N z v w) theta s p := by
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    apply Prod.ext
    · exact add_zero _
    · rfl
  rw [hcoord]
  change N.connection.scalarCurvature N.center * g.inner (centeredNeckLift N theta s p)
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [centeredNeckLift_mfderiv N theta s hp, centeredNeckLift_mfderiv N theta s hp]
  have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 :=
    congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
  simp only [roundCylinderTensorCoefficient, normalizedNeckForm_apply,
    cylinderHeightCovector_basis, hP]
  rfl

theorem centeredNeckMetric_contDiffAt (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    ContDiffAt ℝ ∞
      (centeredCylinderMetric (fun z v w => normalizedNeckForm N z v w) theta s) p := by
  apply ((normalizedNeckMetric N).contDiffAt_pullbackCoefficients
    (centeredNeckLift_contMDiffAt N theta s hp)).congr_of_eventuallyEq
  filter_upwards [(centeredNeckDomain_isOpen N s).mem_nhds hp] with q hq
  exact (normalizedNeckMetric_pullbackCoefficients N theta s hq).symm

theorem exists_centeredNeckMetric_realization (N : EpsilonNeck g)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃} (hp : p ∈ centeredNeckDomain N s) :
    ∃ (gE : RiemannianMetric 3 E₃) (_DE : LeviCivitaData gE) (V : Set E₃),
      IsOpen V ∧ p ∈ V ∧ V ⊆ centeredNeckDomain N s ∧
        ∀ q ∈ V, gE.euclideanCoefficients q =
          (normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N theta s) q := by
  apply RiemannianMetric.exists_local_realization (centeredNeckDomain_isOpen N s) hp
  · intro q hq
    exact ((normalizedNeckMetric N).contDiffAt_pullbackCoefficients
      (centeredNeckLift_contMDiffAt N theta s hq)).contDiffWithinAt
  · intro q _ v w
    exact (normalizedNeckMetric N).symm (centeredNeckLift N theta s q) _ _
  · intro q hq v hv
    apply (normalizedNeckMetric N).pos (centeredNeckLift N theta s q)
    intro hz
    apply hv
    apply (centeredNeckLift_mfderiv_isInvertible N theta s hq).injective
    rw [map_zero]
    exact hz

end PoincareConjecture.M36
