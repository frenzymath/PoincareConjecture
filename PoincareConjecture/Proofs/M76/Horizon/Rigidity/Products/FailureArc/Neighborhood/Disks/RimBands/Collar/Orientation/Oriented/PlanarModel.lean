import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Oriented.EmbeddedSurface
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition







set_option autoImplicit false

open Poincare.Topology.Orientation.ProjectivePlane
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_original_proper_planar_pair_surface_cooriented_charts_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X)
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f K.space)
    (hi : IsEmbedding (fun z : K.space => f z))
    (hne : (interior K.space).Nonempty) (R : Set X)
    (hproper : ∀ z ∈ K.space, f z ∈ frontier R ↔ z ∈ frontier K.space) :
    ∃ E : (f '' K.space \ frontier R : Set X) → OpenPartialHomeomorph X C3,
      (∀ x : (f '' K.space \ frontier R : Set X), (x : X) ∈ (E x).source) ∧
      (∀ i y, y ∈ (E i).source → (y ∈ f '' K.space \ frontier R ↔ (E i y).2 = 0)) ∧
      ∀ i k (x : (f '' K.space \ frontier R : Set X)),
        (x : X) ∈ (E i).source ∩ (E k).source →
          ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
            EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E k y).2) V := by
  let L : V2 ≃L[ℝ] P2 := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let a := L.symm.toContinuousAffineEquiv
  let hA := K.affineOnFaces_affine a.toContinuousAffineMap
  let K' := hA.embeddedImage a.injective.injOn
  have hK' : K'.faces.Finite := hA.embeddedImage_finite _ hK
  have hKs : K'.space = a '' K.space := hA.embeddedImage_space _
  have hmap : MapsTo L K'.space K.space := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hKs ▸ hz
    simpa only [a, ContinuousLinearEquiv.coe_toContinuousAffineEquiv,
      L.apply_symm_apply] using hx
  have hf' : PolyhedralPLInCharts e (f ∘ L) K'.space :=
    hf.comp_finitePiecewiseAffineOn K' hK'
      ⟨K', hK', rfl, K'.affineOnFaces_affine L.toContinuousAffineEquiv.toContinuousAffineMap⟩ hmap
  let J : K'.space ≃ₜ K.space :=
    (Homeomorph.setCongr hKs).trans (a.toHomeomorph.image K.space).symm
  have hi' : IsEmbedding (fun z : K'.space => (f ∘ L) z) := hi.comp J.isEmbedding
  have hne' : (interior K'.space).Nonempty := by
    rw [hKs]
    change (interior (a.toHomeomorph '' K.space)).Nonempty
    rw [← a.toHomeomorph.image_interior K.space]
    exact hne.image a
  have hfront : frontier K'.space = L ⁻¹' frontier K.space := by
    rw [hKs]
    change frontier (a.toHomeomorph '' K.space) = _
    rw [← a.toHomeomorph.image_frontier K.space]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change L (L.symm x) ∈ frontier K.space
      simpa only [L.apply_symm_apply] using hx
    · intro hz
      exact ⟨L z, hz, L.symm_apply_apply z⟩
  have hproper' : ∀ z ∈ K'.space,
      (f ∘ L) z ∈ frontier R ↔ z ∈ frontier K'.space := by
    intro z hz
    rw [hfront]
    exact hproper (L z) (hmap hz)
  have himage : (f ∘ L) '' K'.space = f '' K.space := by
    rw [hKs, image_image]
    apply image_congr
    intro z _
    change f (L (L.symm z)) = f z
    rw [L.apply_symm_apply]
  have h := exists_original_proper_planar_surface_cooriented_charts_of_localOrientation
    O e hcover he K' hK' (f ∘ L) hf' hi' hne' R hproper'
  rw [himage] at h
  exact h

end PoincareConjecture.M76.Dehn.Annuli.RimBands
