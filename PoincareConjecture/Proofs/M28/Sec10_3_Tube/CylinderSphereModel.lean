import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

open M28

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  {U : TopologicalSpace.Opens M}

theorem exists_isotopic_sphere_model
    (T : OpenCylinderModel (U : Set M)) {S : Set M}
    (hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere) :
    ∃ T' : OpenCylinderModel (U : Set M), T'.middleSphere = S := by
  obtain ⟨H, hH, hslice, hzero, hone⟩ := exists_global_smooth_sphere_isotopy hS
  obtain ⟨Ksupport, e, _hK, hKA, he, hes, htransport, hfix⟩ :=
    exists_compact_annulus_sphere_transport T hH hslice
  have hpres (v : E₃) : v ∈ cylinderAnnulus ↔ e v ∈ cylinderAnnulus := by
    constructor
    · intro hv
      by_contra hnot
      have hvK : e v ∉ Ksupport := fun h => hnot (hKA h)
      have heq : e v = v := e.injective (hfix (e v) hvK)
      exact hnot (heq.symm ▸ hv)
    · intro hev
      by_contra hv
      exact hv ((hfix v (fun hk => hv (hKA hk))) ▸ hev)
  have hpres' (v : E₃) (hv : v ∈ cylinderAnnulus) :
      e.symm v ∈ cylinderAnnulus :=
    (hpres (e.symm v)).mpr (by simpa only [e.apply_symm_apply] using hv)
  let A : M → E₃ := fun x => cylinderRadial (T.inverse x)
  let B : E₃ → M := T.annulusAmbientInverse
  have hAU (x : M) (hx : x ∈ U) : A x ∈ cylinderAnnulus :=
    cylinderRadial_mem (T.inverse_mem x hx).2
  have hBA (x : M) (hx : x ∈ U) : B (A x) = x := by
    let xU : U := ⟨x, hx⟩
    change T.annulusAmbientInverse (T.annulusCoordinates xU) = (xU : M)
    rw [T.annulusAmbientInverse_apply
      ⟨T.annulusCoordinates xU, T.annulusCoordinates_mem xU⟩]
    exact T.annulusParametrization_coordinates xU
  have hBU (v : E₃) (hv : v ∈ cylinderAnnulus) : B v ∈ U := by
    change T.annulusAmbientInverse v ∈ U
    rw [T.annulusAmbientInverse_apply ⟨v, hv⟩]
    exact T.annulusParametrization_mem _
  have hAB (v : E₃) (hv : v ∈ cylinderAnnulus) : A (B v) = v := by
    change A (T.annulusAmbientInverse v) = v
    rw [T.annulusAmbientInverse_apply ⟨v, hv⟩]
    exact T.annulusCoordinates_parametrization ⟨v, hv⟩
  have hAs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A (U : Set M) :=
    contMDiff_cylinderRadial.comp_contMDiffOn T.inverse_smooth
  let F : M → M := fun x => B (e.symm (A x))
  let G : M → M := fun x => B (e (A x))
  have hFU (x : M) (hx : x ∈ U) : F x ∈ U := hBU _ (hpres' _ (hAU x hx))
  have hGU (x : M) (hx : x ∈ U) : G x ∈ U := hBU _ ((hpres _).mp (hAU x hx))
  have hFs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F (U : Set M) :=
    T.contMDiffOn_annulusAmbientInverse.comp
      (hes.contMDiff.comp_contMDiffOn hAs) (fun x hx => hpres' _ (hAU x hx))
  have hGs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ G (U : Set M) :=
    T.contMDiffOn_annulusAmbientInverse.comp
      (he.contMDiff.comp_contMDiffOn hAs) (fun x hx => (hpres _).mp (hAU x hx))
  have hFG (x : M) (hx : x ∈ U) : F (G x) = x := by
    dsimp only [F, G]
    rw [hAB _ ((hpres _).mp (hAU x hx)), e.symm_apply_apply, hBA x hx]
  have hGF (x : M) (hx : x ∈ U) : G (F x) = x := by
    dsimp only [F, G]
    rw [hAB _ (hpres' _ (hAU x hx)), e.apply_symm_apply, hBA x hx]
  let eA : cylinderAnnulus ≃ₜ cylinderAnnulus := e.subtype hpres
  let eU : U ≃ₜ U :=
    (T.annulusHomeomorph.trans eA.symm).trans T.annulusHomeomorph.symm
  have heU (x : U) : (eU x : M) = F x := by
    exact (T.annulusAmbientInverse_apply (eA.symm (T.annulusHomeomorph x))).symm
  let T' : OpenCylinderModel (U : Set M) := {
    homeomorph := T.homeomorph.trans eU
    coordinate := fun z => F (T.coordinate z)
    coordinate_eq := fun z => by
      change (eU (T.homeomorph z) : M) = _
      rw [heU, T.coordinate_eq]
    coordinate_smooth := hFs.comp T.coordinate_smooth
      (fun z hz => T.coordinate_mem_m28 hz.2)
    inverse := fun x => T.inverse (G x)
    inverse_mem := fun x hx => T.inverse_mem _ (hGU x hx)
    left_inverse := by
      intro z hz
      change T.inverse (G (F (T.coordinate z))) = z
      rw [hGF _ (T.coordinate_mem_m28 hz.2)]
      exact T.left_inverse hz
    right_inverse := by
      intro x hx
      change F (T.coordinate (T.inverse (G x))) = x
      rw [T.right_inverse (hGU x hx)]
      exact hFG x hx
    inverse_smooth := T.inverse_smooth.comp hGs hGU }
  have hGH (q : UnitTwoSphere) : G (H (0, q)) = H (1, q) := by
    change B (e (cylinderRadial (T.inverse (H (0, q))))) = H (1, q)
    rw [htransport]
    exact hBA _ ((hslice 1).2 (mem_range_self q))
  have hFH (q : UnitTwoSphere) : F (H (1, q)) = H (0, q) := by
    rw [← hGH]
    exact hFG _ ((hslice 0).2 (mem_range_self q))
  refine ⟨T', ?_⟩
  have hmiddle : T'.middleSphere = F '' T.middleSphere :=
    (image_image F T.coordinate (univ ×ˢ ({1 / 2} : Set ℝ))).symm
  rw [hmiddle, ← hone, ← hzero]
  ext x
  constructor
  · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
    rw [hFH]
    exact mem_range_self q
  · rintro ⟨q, rfl⟩
    exact ⟨H (1, q), mem_range_self q, hFH q⟩

end PoincareConjecture.OpenCylinderModel
