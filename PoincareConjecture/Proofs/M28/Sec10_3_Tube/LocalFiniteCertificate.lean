import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFiniteBalanced
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCylinderCertificate

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_finite_openCylinderModel_threshold_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, C.shape = .finite a b →
        ∃ T : OpenCylinderModel (C.unionOpen : Set M),
          ∀ i ∈ C.shape.active, SmoothSphereIsotopicIn (C.unionOpen : Set M)
            (C.neck i).central_sphere T.middleSphere := by
  obtain ⟨ε₁, hε₁, hsmall, hfinite⟩ := exists_finite_cylinder_with_middle_threshold_m28.{u}
  obtain ⟨ε₂, hε₂, _, hmodel⟩ := exists_openCylinderModel_of_middle_slice_threshold_m28.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε a b hshape
  obtain ⟨D, j, hj, c, hc, hDzero⟩ := hfinite C
    (hε.trans (min_le_left _ _)) a b hshape
  exact hmodel C (hε.trans (min_le_right _ _)) D j hj c hc hDzero

theorem exists_finite_tubeCertificate_threshold_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, C.shape = .finite a b →
        ∀ X : Set M, X ⊆ (C.unionOpen : Set M) →
        ∃ T : EpsilonTubeCertificate g X,
          T.epsilon = ε ∧ HEq T.chain C ∧ T.carrier = (C.unionOpen : Set M) := by
  obtain ⟨ε₀, hε₀, hsmall, hmodel⟩ := exists_finite_openCylinderModel_threshold_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε a b hshape X hX
  obtain ⟨T, hT⟩ := hmodel C hε a b hshape
  let certificate : EpsilonTubeCertificate g X :=
    C.tubeCertificateOfCylinder_m28 (hε.trans hsmall) T hT X hX
  exact ⟨certificate, rfl, HEq.rfl, rfl⟩

end PoincareConjecture.BalancedNeckChain
