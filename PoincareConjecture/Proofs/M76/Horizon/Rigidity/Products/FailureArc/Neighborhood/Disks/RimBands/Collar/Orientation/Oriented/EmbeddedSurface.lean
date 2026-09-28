import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.OriginalSurfaceAtlas
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Oriented.Normal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.PlanarSourceChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.OriginalTangentCoordinates

set_option autoImplicit false

open Poincare.Topology.Orientation.ProjectivePlane
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_embedded_planar_surface_cooriented_charts_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X)
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j K.space)
    (hi : IsEmbedding (fun z : K.space => j z))
    (hne : (interior K.space).Nonempty) :
    ∃ E : (j '' interior K.space) → OpenPartialHomeomorph X C3,
      (∀ x : j '' interior K.space, (x : X) ∈ (E x).source) ∧
      (∀ i y, y ∈ (E i).source → (y ∈ j '' interior K.space ↔ (E i y).2 = 0)) ∧
      ∀ i k (x : j '' interior K.space), (x : X) ∈ (E i).source ∩ (E k).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E k y).2) V := by
  classical
  let S := j '' interior K.space
  let : Nonempty S := ⟨⟨j hne.choose, mem_image_of_mem j hne.choose_spec⟩⟩
  obtain ⟨A, _, _, hA, hAPL⟩ :=
    exists_original_planar_interior_flattening_atlas e hcover he K hK j hj hi
  have hi₀ : IsEmbedding (fun z : interior K.space => j z) :=
    hi.comp (IsEmbedding.inclusion interior_subset)
  have hrange : range (fun z : interior K.space => j z) = S := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact mem_image_of_mem j z.property
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let J₀ : interior K.space ≃ₜ S := hi₀.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let L : V2 ≃L[ℝ] P2 := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let Q := L '' interior K.space
  have hQ : IsOpen Q := L.toHomeomorph.isOpenMap _ isOpen_interior
  let J : Q ≃ₜ S := (L.toHomeomorph.image (interior K.space)).symm.trans J₀
  have hJ (z : Q) : (J z : X) = j (L.symm z) := rfl
  let f := fun i z => (A.chart i (j (L.symm z))).1
  have hf (i : S) (z : Q) : f i z = atlasTangentialChart A i (J z) := by
    change (A.chart i (j (L.symm z))).1 = (A.chart i (J z : X)).1
    rw [hJ]
  have hdomain (i : S) :
      (Subtype.val : Q → P2) '' (J ⁻¹' (atlasTangentialChart A i).source) =
        L.symm ⁻¹' (interior K.space ∩ j ⁻¹' (A.chart i).source) := by
    ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzQ : L.symm z ∈ interior K.space := by
        obtain ⟨w, hw, hwz⟩ := z.property
        rw [← hwz, L.symm_apply_apply]
        exact hw
      change (J z : X) ∈ (A.chart i).source at hz
      rw [hJ] at hz
      exact ⟨hzQ, hz⟩
    · rintro ⟨hz, hzi⟩
      have hzQ : z ∈ Q := ⟨L.symm z, hz, L.apply_symm_apply z⟩
      refine ⟨⟨z, hzQ⟩, ?_, rfl⟩
      change (J ⟨z, hzQ⟩ : X) ∈ (A.chart i).source
      rw [hJ]
      exact hzi
  have hfPL (i : S) : LocallyPiecewiseAffineOn (f i)
      ((Subtype.val : Q → P2) '' (J ⁻¹' (atlasTangentialChart A i).source)) := by
    rw [hdomain]
    have h := hj.locallyPiecewiseAffineOn_tangent_chart_comp_interior hK
      (A.chart i) (fun a => (hA a i).1)
    have hL := locallyPiecewiseAffineOn_affine L.symm.toContinuousAffineEquiv.toContinuousAffineMap
      isOpen_univ
    have hh := h.comp hL
    simp only [univ_inter] at hh
    exact hh
  obtain ⟨b, hb, _, _, _, hbPL⟩ := exists_global_chart_of_open_parametrization hQ J
    (atlasTangentialChart A) f hf hfPL
  exact exists_original_planar_surface_cooriented_charts_of_localOrientation O A hAPL b hb hbPL

theorem exists_original_proper_planar_surface_cooriented_charts_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X)
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j K.space)
    (hi : IsEmbedding (fun z : K.space => j z))
    (hne : (interior K.space).Nonempty) (R : Set X)
    (hproper : ∀ z ∈ K.space, j z ∈ frontier R ↔ z ∈ frontier K.space) :
    ∃ E : (j '' K.space \ frontier R : Set X) → OpenPartialHomeomorph X C3,
      (∀ x : (j '' K.space \ frontier R : Set X), (x : X) ∈ (E x).source) ∧
      (∀ i y, y ∈ (E i).source → (y ∈ j '' K.space \ frontier R ↔ (E i y).2 = 0)) ∧
      ∀ i k (x : (j '' K.space \ frontier R : Set X)), (x : X) ∈ (E i).source ∩ (E k).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E k y).2) V := by
  have hS : j '' interior K.space = j '' K.space \ frontier R := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨mem_image_of_mem j (interior_subset hz), ?_⟩
      intro hfront
      exact ((hproper z (interior_subset hz)).mp hfront).2 hz
    · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
      refine ⟨z, ?_, rfl⟩
      by_contra hn
      exact hnot ((hproper z hz).mpr ⟨subset_closure hz, hn⟩)
  exact hS ▸ exists_embedded_planar_surface_cooriented_charts_of_localOrientation O e hcover he K hK j hj hi hne

end PoincareConjecture.M76.Dehn.Annuli.RimBands
