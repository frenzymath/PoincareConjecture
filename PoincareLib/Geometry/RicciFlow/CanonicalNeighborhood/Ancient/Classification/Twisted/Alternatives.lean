import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Twisted.Construction
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Tube.Assembly
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.Twisted
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Alternatives

/-!
# The exact twisted-cylinder alternative from M27 services

The explicit slab cap and its attached positive-end tube give the original
flow's capped-quotient branch. Every point outside the open core, including
the core boundary, centers a strong neck with the same epsilon.

Reference: Morgan--Tian, Theorem 9.93(5), p. 242.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

/-- The same explicit cap retained in the whole tube supplies all cap-core
or strong-neck coverage, including at every point of its core boundary. -/
theorem AncientKappaCapServices.exists_strongCappedTube_coverage
    (P : AncientKappaCapServices.{u}) (model : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 200) :
    ∃ tube : M26StrongCappedTube K t epsilon (P.twistedCapConstant epsilon),
      ∀ x : M, x ∈ tube.cap.cap.core ∨
        ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  classical
  let q : UnitTwoSphere := Classical.arbitrary _
  obtain ⟨_, a, ha⟩ := model.exists_scalarNormalized_sphere ht (q, 0)
  let cap := P.uniformSlabCap model ht hε hsmall q a ha
  let tube := model.cappedTubeOfSlabCap ht hε hsmall q a ha cap
    (P.uniformSlabCap_carrier model ht hε hsmall q a ha)
    (P.uniformSlabCap_end_neck_carrier model ht hε hsmall q a ha)
  have hstrong : ∀ x ∈ tube.tube.carrier,
      ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
    intro x hx
    exact model.strong_necks_outside_slabCore ht hε (by linarith)
      (model.cover (q, 0)) x hx
  refine ⟨NoncompactKappa.strongCappedTubeOfCappedTube K ht tube
    rfl rfl le_rfl hstrong rfl, ?_⟩
  intro x
  by_cases hx : x ∈ cap.core
  · exact Or.inl hx
  · exact Or.inr (model.strong_necks_outside_interior_slabCore ht hε
      (by linarith) (model.cover (q, 0)) x hx)

/-- The capped-quotient branch with constants fixed before the solution,
using exactly the common analytic fields in the frozen M27 bundle. -/
theorem m27TwistedAlternatives (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M) (_model : M27TwistedSphereLineFlowCertificate K),
            M27KappaNine93Conclusion K epsilon C := by
  refine ⟨1 / 200, by norm_num, le_rfl, ?_⟩
  intro epsilon hε hsmall
  refine ⟨P.capServices.twistedCapConstant epsilon,
    P.capServices.twistedCapConstant_pos hε, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K model
  obtain ⟨tube, hcoverage⟩ :=
    P.capServices.exists_strongCappedTube_coverage model le_rfl hε hsmall
  exact .cappedQuotient model tube hcoverage

end PoincareMT
