import PoincareLib.Geometry.RicciFlow.Soliton.Models.Refined
import PoincareLib.Geometry.RicciFlow.Soliton.Models.Involution.Formula
import PoincareLib.Geometry.RicciFlow.Soliton.Models.Involution.ProjectivePlane
import PoincareLib.Geometry.RicciFlow.Soliton.Models.Involution.Twisted

/-!
# Normal forms of free shrinking-cylinder quotients

Every supplied quotient receives the literal normal form and commuting
coordinates on its own carrier required by the frozen M24 definitions.
Morgan--Tian, Theorem 9.42 and (9.19), pp. 206-208; Proposition 9.58,
pp. 220-221.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_quotientNormalForm
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (q : QuotientSphereLineCertificate G) :
    Nonempty (M24QuotientNormalForm q) := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.surface_charted
  let := q.product.surface_manifold
  rcases q.involution_eq_antipodal_identity_or_reflection with h | ⟨c, h⟩
  · obtain ⟨e, he⟩ := q.exists_projectivePlaneCoordinates realProjectiveTwoSetoid
      (fun _ _ => Iff.rfl) h
    exact ⟨.projectivePlaneLine ⟨h, e, he⟩⟩
  · obtain ⟨e, cover, he⟩ := q.exists_twistedProjectiveSmoothModel c h
    exact ⟨.twistedSphereLine ⟨c, h, twistedProjectivePuncture, e, cover, he⟩⟩

/-- Use the constructed normal form in the actual M24 quotient branch,
retaining the supplied quotient and its independently constructed transports. -/
theorem exists_refinedQuotientCertificate
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (q : QuotientSphereLineCertificate G) (transport : M24QuotientFlowTransport q) :
    ∃ c : RepairedKappaModelCertificate G,
      M24CertificateMatches (.quotientSphereLine q) c := by
  obtain ⟨normal⟩ := exists_quotientNormalForm q
  exact ⟨.quotientSphereLine q transport normal, rfl⟩

end PoincareMT
