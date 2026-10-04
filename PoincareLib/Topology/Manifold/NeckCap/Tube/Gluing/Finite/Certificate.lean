import PoincareLib.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Balanced
import PoincareLib.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Certificate

/-!
# Tube certificates for finite balanced neck chains

The actual finite gluing has a selected neck slice as its zero sphere.
Normalizing this cylinder to the frozen model and composing the selected
sphere isotopies gives every field of the frozen tube certificate. The
certificate retains the given chain, including its supplied source necks.

Reference: Morgan--Tian, Proposition A.19, pp. 507--508, finite-chain case.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareMT.BalancedNeckChain

/-- The frozen cylinder model of a sufficiently small finite balanced chain
has all the selected central-sphere isotopies in its exact carrier union. -/
theorem exists_finite_openCylinderModel_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, C.shape = .finite a b →
        ∃ T : OpenCylinderModel (C.unionOpen : Set M),
          ∀ i ∈ C.shape.active, SmoothSphereIsotopicIn (C.unionOpen : Set M)
            (C.neck i).central_sphere T.middleSphere := by
  obtain ⟨ε₁, hε₁, hsmall, hfinite⟩ := exists_finite_cylinder_with_middle_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hmodel⟩ := exists_openCylinderModel_of_middle_slice_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε a b hshape
  obtain ⟨D, j, hj, c, hc, hDzero⟩ := hfinite C
    (hε.trans (min_le_left _ _)) a b hshape
  exact hmodel C (hε.trans (min_le_right _ _)) D j hj c hc hDzero

/-- Every covered subset of a sufficiently small finite balanced chain has
the frozen tube certificate, retaining precisely the given chain. -/
theorem exists_finite_tubeCertificate_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, C.shape = .finite a b →
        ∀ X : Set M, X ⊆ (C.unionOpen : Set M) →
        ∃ T : EpsilonTubeCertificate g X,
          T.epsilon = ε ∧ HEq T.chain C ∧ T.carrier = (C.unionOpen : Set M) := by
  obtain ⟨ε₀, hε₀, hsmall, hmodel⟩ := exists_finite_openCylinderModel_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε a b hshape X hX
  obtain ⟨T, hT⟩ := hmodel C hε a b hshape
  let certificate : EpsilonTubeCertificate g X :=
    C.tubeCertificateOfCylinder (hε.trans hsmall) T hT X hX
  exact ⟨certificate, rfl, HEq.rfl, rfl⟩

end PoincareMT.BalancedNeckChain
