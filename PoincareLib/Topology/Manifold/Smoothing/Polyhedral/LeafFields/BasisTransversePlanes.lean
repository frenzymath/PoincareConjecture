import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.BasisProjectionConverse
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.ComplementPlaneCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.SecantTransversality

/-!
# Transverse planes of independent source stars

Geometric secant transversality is equivalent to the radial realization
condition on basis images. Restricting the complementary-plane
homeomorphism therefore gives the actual transverse-plane coordinates.
See Cairns 1940, pp. 799--801, and M76 derivation 30.
-/

set_option autoImplicit false

open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Planes transverse to the source set and complementary to the
specified coordinate plane, in geometric projector topology.
See Cairns pp. 799--801 and M76 derivation 30. -/
abbrev TransverseComplementPlaneSpace (U : Submodule ℝ E) (S : Set E) :=
  {K : U.ComplementPlaneSpace // K.val.subspace.IsSecantTransverse S}

/-- The complementary-plane correspondence restricts to transverse
kernels with their actual geometric secant condition.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def transversePlaneRetractionHomeomorph (U : Submodule ℝ E) (S : Set E) :
    U.TransverseComplementPlaneSpace S ≃ₜ
      {Q : U.RetractionSpace // Q.val.ker.IsSecantTransverse S} :=
  U.complementPlaneHomeomorph.subtype (fun K => by
    change K.val.subspace.IsSecantTransverse S ↔
      (U.complementRetraction K).val.ker.IsSecantTransverse S
    rw [U.ker_complementRetraction K])

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The kernel-plane angle condition is exactly faithful radial
realization for the images of the independent source vertices.
See Cairns pp. 799--801 and M76 derivation 30. -/
theorem isRadialEmbedding_iff_isSecantTransverse_ker (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      Q.ker.IsSecantTransverse (A.basisRadialEmbedding b).cone.space := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ :=
      BasisRadialProjection.exists_pos_secant_bound (⟨Q, h⟩ : A.BasisRadialProjection b F)
    exact Submodule.isSecantTransverse_ker_of_lower_bound Q hc hb
  · intro h
    exact A.isRadialEmbedding_of_injOn_basisCone b Q (h.injOn Q rfl)

/-- Transverse planes of a full basis star are homeomorphic to radial
retractions onto the chosen coordinate plane. Both topologies are
the pre-existing geometric and operator subspace topologies.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def basisTransversePlaneHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (U : Submodule ℝ E) :
    U.TransverseComplementPlaneSpace (A.basisRadialEmbedding b).cone.space ≃ₜ
      {Q : U.RetractionSpace // A.IsRadialEmbedding (fun i => Q.val (b i))} :=
  (U.transversePlaneRetractionHomeomorph (A.basisRadialEmbedding b).cone.space).trans
    (Homeomorph.setCongr (by
      ext Q
      exact (A.isRadialEmbedding_iff_isSecantTransverse_ker b Q.val).symm))

end AbstractSimplicialComplex
