import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.Germ

/-!
# Matching a prescribed sphere collar

Global cylinder coordinates agreeing with a prescribed collar on the central
sphere can be adjusted to agree on a whole smaller collar.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare

open PoincareMT

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- Matching the sphere parametrization suffices to match a smaller whole
collar, without any further hypothesis on the complementary sides. -/
theorem exists_cylinder_extension_of_sphere_agreement
    {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
    {δ : ℝ} (hδ : 0 < δ)
    (c : OpenPartialHomeomorph RoundCylinderSpace Y)
    (hsource : (univ : Set UnitTwoSphere) ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    (G : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace Y ∞)
    (hG : ∀ q : UnitTwoSphere, G (q, 0) = c (q, 0)) :
    ∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace Y ∞,
        ∀ p : RoundCylinderSpace, |p.2| < η → F p = c p := by
  let e := c.trans G.symm.toHomeomorph.toOpenPartialHomeomorph
  have hes : e.source = c.source := by
    simp [e]
  have hef (p : RoundCylinderSpace) : e p = G.symm (c p) := rfl
  have hei (p : RoundCylinderSpace) : e.symm p = c.symm (G p) := rfl
  have het (p : RoundCylinderSpace) (hp : p ∈ e.target) : G p ∈ c.target := hp.2
  have he : ContMDiffOn CylModel CylModel ∞ e e.source := by
    rw [hes]
    exact G.symm.contMDiff.comp_contMDiffOn hc
  have heinv : ContMDiffOn CylModel CylModel ∞ e.symm e.target :=
    hci.comp G.contMDiff.contMDiffOn het
  obtain ⟨η, hη, hηδ, K, hK⟩ := exists_cylinder_collar_extension_of_fixing_zero hδ e
    (hes ▸ hsource) he heinv (fun q => by rw [hef, ← hG, G.symm_apply_apply])
  refine ⟨η, hη, hηδ, K.trans G, ?_⟩
  intro p hp
  change G (K p) = c p
  rw [hK p hp, hef, G.apply_symm_apply]

end Poincare
