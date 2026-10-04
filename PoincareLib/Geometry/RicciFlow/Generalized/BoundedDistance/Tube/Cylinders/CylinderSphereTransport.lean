import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderAnnulus
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Spheres.SphereAmbientTransport
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.SmoothSphereIsotopy

/-!
# Ambient sphere transport in the actual cylinder coordinates

Morgan--Tian Claim 10.3, pp. 248-249, and Hirsch, Differential Topology,
Theorem 8.1.3, p. 180. The supplied embeddings are rectified on the original
manifold. Composing their actual local retractions with the literal annulus
inverse supplies the Euclidean displacement construction. No embedding
composition theorem, separator, or ambient extension is assumed.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  {U : TopologicalSpace.Opens M}

/-- Actual embeddings in the original open cylinder produce a compactly
supported ambient transport of their literal annulus images. The compact
set is auxiliary support only (Hirsch 8.1.3, p. 180; MT Claim 10.3). -/
theorem exists_compact_annulus_sphere_transport
    (T : OpenCylinderModel (U : Set M)) {H : ℝ × UnitTwoSphere → M}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H)
    (hslice : ∀ t : ℝ,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => H (t, q)) ∧
        range (fun q => H (t, q)) ⊆ U) :
    ∃ (Ksupport : Set E₃) (e : E₃ ≃ₜ E₃),
      IsCompact Ksupport ∧ Ksupport ⊆ cylinderAnnulus ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ q : UnitTwoSphere,
        e (cylinderRadial (T.inverse (H (0, q)))) =
          cylinderRadial (T.inverse (H (1, q)))) ∧
      ∀ x : E₃, x ∉ Ksupport → e x = x := by
  let F : ℝ × UnitTwoSphere → E₃ := fun p => cylinderRadial (T.inverse (H p))
  have hHU (p : ℝ × UnitTwoSphere) : H p ∈ U :=
    (hslice p.1).2 (mem_range_self p.2)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ F :=
    contMDiff_cylinderRadial.comp (T.inverse_smooth.comp_contMDiff hH hHU)
  have hFA (p : ℝ × UnitTwoSphere) : F p ∈ cylinderAnnulus :=
    cylinderRadial_mem (T.inverse_mem (H p) (hHU p)).2
  have hBF (p : ℝ × UnitTwoSphere) : T.annulusAmbientInverse (F p) = H p := by
    let x : U := ⟨H p, hHU p⟩
    change T.annulusAmbientInverse (T.annulusCoordinates x) = (x : M)
    rw [T.annulusAmbientInverse_apply
      ⟨T.annulusCoordinates x, T.annulusCoordinates_mem x⟩]
    exact T.annulusParametrization_coordinates x
  have hlocal (t : ℝ) (q : UnitTwoSphere) :
      ∃ (W : Set E₃) (r' : E₃ → UnitTwoSphere),
        IsOpen W ∧ F (t, q) ∈ W ∧ W ⊆ cylinderAnnulus ∧
        ContMDiffOn (𝓡 3) (𝓡 2) ∞ r' W ∧
        ∀ z : UnitTwoSphere, F (t, z) ∈ W → r' (F (t, z)) = z := by
    obtain ⟨V, r, hVo, hVq, _hVU, hr, hret⟩ :=
      exists_sphere_embedding_local_retraction (hslice t).1 q U.isOpen (hHU (t, q))
    let W : Set E₃ := (cylinderAnnulus : Set E₃) ∩ T.annulusAmbientInverse ⁻¹' V
    have hWo : IsOpen W :=
      T.contMDiffOn_annulusAmbientInverse.continuousOn.isOpen_inter_preimage
        cylinderAnnulus.isOpen hVo
    have hqW : F (t, q) ∈ W := ⟨hFA (t, q), by
      change T.annulusAmbientInverse (F (t, q)) ∈ V
      rw [hBF]
      exact hVq⟩
    refine ⟨W, r ∘ T.annulusAmbientInverse, hWo, hqW, inter_subset_left,
      hr.comp (T.contMDiffOn_annulusAmbientInverse.mono inter_subset_left)
        inter_subset_right, ?_⟩
    intro z hz
    change r (T.annulusAmbientInverse (F (t, z))) = z
    rw [hBF]
    apply hret z
    have hzV := hz.2
    change T.annulusAmbientInverse (F (t, z)) ∈ V at hzV
    rwa [hBF] at hzV
  exact exists_compact_sphere_ambient_transport hF (cylinderAnnulus : Set E₃)
    (fun t _ => hlocal t)

end PoincareMT.M28
