import PoincareConjecture.Proofs.M76.Triangulation.AlexanderInitialRegionInduction
import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FiniteGenericHeight











set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]







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
