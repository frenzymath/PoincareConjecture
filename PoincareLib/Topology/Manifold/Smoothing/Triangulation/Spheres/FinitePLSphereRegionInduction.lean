import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Regions.AlexanderInitialRegionInduction
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Spheres.FinitePLSphereIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.FiniteGenericHeight

/-!
# Region induction for an actual finite PL sphere

The original sphere model supplies the actual finite surface
complex. A separating vertex height gives its initial profile,
so the full region induction needs only the explicit zero-charge
supplier. See Alexander 1924, pp. 6--8, Cairns 1940,
pp. 798--800 and M76 derivations 272 and 278d.
-/

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every actual finite PL sphere inside the given convex
outer body has both region-ball certificates once the explicit
zero-charge supplier is available. The triangulation, generic
height, initial profile and positive-event recursion are all
constructed from this same sphere. See Alexander pp. 6--8
and M76 derivation 278d. -/
theorem IsFinitePL.hasAlexanderRegionBalls_of_zero_charge_supplier
    {S : Set E} {D : Set F} {e : S ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hDcv : Convex ℝ D) (hDne : (interior D).Nonempty)
    (hdimD : Module.finrank ℝ F = 3) (hdim : Module.finrank ℝ E = 3)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hSC : S ⊆ interior C)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJC : J.space = C)
    (base : ∀ W : AlexanderSectionProfile E,
      W.HasNonisolatedHeightSigns → W.HasFiniteHeightSignEvents →
      (∀ c, W.charge c = 0) → W.carrier ⊆ interior C →
      (∃ e : W.carrier ≃ₜ frontier (halfBall 1), e.IsFinitePL) →
      HasAlexanderRegionBalls W.carrier C) :
    HasAlexanderRegionBalls S C := by
  classical
  obtain ⟨K, hK, hKS, _, hpure, hcofaces, _⟩ :=
    he.exists_height_aligned_surface_complex hD hDcv hDne hdimD (0 : E →ᵃ[ℝ] ℝ)
  obtain ⟨L, hL⟩ := (K.finite_vertices_of_finite_faces hK).exists_linearMap_injOn (K := ℝ)
  let eK : K.space ≃ₜ frontier D := (Homeomorph.setCongr hKS).trans e
  have heK : eK.IsFinitePL :=
    (isFinitePL_setCongr hKS K hK rfl).trans he
  have hKC : K.space ⊆ interior C := hKS.symm ▸ hSC
  have hresult := K.hasAlexanderRegionBalls_of_generic_zero_charge_supplier hK
    hdim L.toAffineMap hL hpure hcofaces hD hDcv hDne hdimD eK heK
    hC hcv hne hKC J hJ hJC base
  exact hKS ▸ hresult

end Homeomorph
