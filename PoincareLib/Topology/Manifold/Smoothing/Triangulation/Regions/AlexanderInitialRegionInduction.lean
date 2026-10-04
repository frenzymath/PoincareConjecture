import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Regions.AlexanderRegionInduction
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.General.AlexanderInitialNonisolatedSigns
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Spheres.StandardFinitePLSphereModel

/-!
# Actual generic-surface region induction with a zero-case supplier

The initial surface supplies its own complete profile and all
three event conditions. Standardizing its existing finite PL
sphere model connects it to the same-model recursive induction
inside the unchanged outer body. See Alexander 1924, pp. 6--8
and M76 derivations 276, 278c and 278d.
-/

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The literal initial generic finite surface has both
actual region-ball certificates once the explicit zero-charge
supplier is available. Its recursive split, all successor
conditions and same-map reconstruction are constructed by
the preceding induction. See Alexander pp. 6--8 and
M76 derivation 278d. -/
theorem hasAlexanderRegionBalls_of_generic_zero_charge_supplier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {D : Set F} (hD : IsCompact D) (hDcv : Convex ℝ D)
    (hDne : (interior D).Nonempty) (hdimD : Module.finrank ℝ F = 3)
    (e : K.space ≃ₜ frontier D) (he : e.IsFinitePL)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hKC : K.space ⊆ interior C)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJC : J.space = C)
    (base : ∀ W : AlexanderSectionProfile E,
      W.HasNonisolatedHeightSigns → W.HasFiniteHeightSignEvents →
      (∀ c, W.charge c = 0) → W.carrier ⊆ interior C →
      (∃ e : W.carrier ≃ₜ frontier (halfBall 1), e.IsFinitePL) →
      HasAlexanderRegionBalls W.carrier C) :
    HasAlexanderRegionBalls K.space C := by
  obtain ⟨W, hWK, hWA, _, hfinite, hsigns, hbranching, hnonisolated⟩ :=
    K.exists_initial_alexanderSectionProfile_with_nonisolated_signs A hK hA hpure hcofaces
  have hevents : W.HasFiniteHeightSignEvents := by
    refine ⟨A '' K.vertices, hfinite, ?_⟩
    simpa only [hWA] using hsigns
  have hWC : W.carrier ⊆ interior C := hWK.symm ▸ hKC
  have hmodel : ∃ f : W.carrier ≃ₜ frontier (halfBall 1), f.IsFinitePL := by
    rw [hWK]
    exact he.exists_standard_three_sphere_model hD hDcv hDne hdimD
  have hresult := AlexanderSectionProfile.hasAlexanderRegionBalls_of_zero_charge_supplier
    hdim hC hcv hne J hJ hJC base W hbranching hnonisolated hevents hWC hmodel
  exact hWK ▸ hresult

end Geometry.SimplicialComplex
