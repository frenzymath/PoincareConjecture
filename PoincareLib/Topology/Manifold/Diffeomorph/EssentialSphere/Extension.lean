import PoincareLib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.CollarMatching
import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.AmbientTransport
import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.Embedding
import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.Euclidean

/-!
# Extending essential sphere collars across a cylinder

This is the precise relative straightening statement used by the second-cap
overlap construction. Ambient coordinates follow from filling the compact
Euclidean side and globalizing its collar-matched ball coordinates. The proof
retains the tracked Schoenflies and sphere-isotopy dependencies.

Reference: Hatcher, Notes on Basic 3-Manifold Topology (2014), Section 1.1,
Theorem 1.1, pp. 1--5, and sphere extension, p. 5.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare

/-- An essential collared sphere in an open three-cylinder has global
cylinder coordinates agreeing with its prescribed collar near height zero. -/
theorem exists_essential_sphere_collar_extension
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
    (T : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) Y ∞)
    {δ : ℝ} (hδ : 0 < δ)
    (c : OpenPartialHomeomorph
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) Y)
    (hsource : c.source = Set.univ ×ˢ Set.Ioo (-δ) δ)
    (hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ c.symm c.target)
    (A B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (hcA : IsConnected A) (hcB : IsConnected B) (hdis : Disjoint A B)
    (hcover : A ∪ B =
      (Set.range (fun q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        c (q, 0)))ᶜ)
    (hescape : ∀ L : Set Y, IsCompact L → ¬ A ⊆ L ∧ ¬ B ⊆ L) :
    ∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) Y ∞,
        ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
          |p.2| < η → F p = c p := by
  let J := T.symm.trans sphereCylinderDiffeomorphPunctured
  obtain ⟨F, hF⟩ :
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3)
          (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞,
        ∀ q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          F q = (J (c (q, 0)) : EuclideanSpace ℝ (Fin 3)) := by
    let C : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) Y ∞ := {
      toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := hc
      contMDiffOn_invFun := hci }
    let d := (C.trans T.symm.toPartialDiffeomorph).trans radialPartialDiffeomorph
    have hds : d.source = c.source := by
      ext p
      simp [d, C, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph]
    exact exists_ambient_map_of_euclidean_sphere_collar d.toOpenPartialHomeomorph
      d.contMDiffOn_toFun d.contMDiffOn_invFun hδ (hds.trans hsource)
  obtain ⟨G, hG⟩ := exists_cylinder_coordinates_of_ambient_sphere_in_model
    J (fun q => c (q, 0)) F hF A B hcA.isPreconnected hcB.isPreconnected hcover hescape
  exact exists_cylinder_extension_of_sphere_agreement hδ c hsource.ge hc hci G hG

end Poincare
