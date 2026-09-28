import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckTransfer
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}

noncomputable def pullbackNeckGeometry
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (D : LeviCivitaData g)
    (hscalar : 0 < D.scalarCurvature (e.symm N.center)) :
    NeckGeometryCore g N.epsilon := by
  classical
  let V : Set M := e.symm '' N.carrier
  have hVopen : IsOpen V :=
    e.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target N.carrier_open hcapture
  let H := e.toOpenPartialHomeomorph.symm.homeomorphOfImageSubsetSource
    hcapture (rfl : e.symm '' N.carrier = V)
  have hH_apply (y : N.carrier) : (H y : M) = e.symm y := rfl
  let tmap : UnitTwoSphere × ℝ → M := fun z => e.symm (N.coordinate_map z)
  let tinv : M → UnitTwoSphere × ℝ := fun x => N.coordinate_inverse (e x)
  have hcoord_mem : ∀ z : UnitTwoSphere × ℝ,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → N.coordinate_map z ∈ e.target :=
    fun z hz => hcapture (N.coordinate_map_mem_of_axial z hz)
  have hVsource : V ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcapture hy)
  have hright (y : X) (hy : y ∈ e.target) : e (e.symm y) = y := e.right_inv hy
  have hmap_to_carrier : MapsTo e V N.carrier := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hright y (hcapture hy)]
    exact hy
  have hcoord_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ tmap
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    e.contMDiffOn_invFun.comp N.coordinate_map_smooth (fun z hz => hcoord_mem z hz.2)
  have hinv_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ tinv V :=
    N.coordinate_inverse_smooth.comp (e.contMDiffOn_toFun.mono hVsource) hmap_to_carrier
  refine {
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := (D.scalarCurvature (e.symm N.center)) ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hscalar _
    center := e.symm N.center
    connection := D
    scalar_center_pos := hscalar
    scale_eq_scalar := rfl
    carrier := V
    carrier_open := hVopen
    coordinate := N.coordinate.trans H
    coordinate_map := tmap
    coordinate_map_eq := ?_
    coordinate_map_smooth := hcoord_smooth
    coordinate_inverse := tinv
    coordinate_inverse_mem := ?_
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := hinv_smooth
    central_sphere := e.symm '' N.central_sphere
    central_sphere_eq := ?_
    center_on_central_sphere := ?_
    central_sphere_subset := ?_ }
  · intro z
    change H (N.coordinate z) = tmap (z.1, (z.2 : ℝ))
    dsimp [H, tmap]
    change e.symm (N.coordinate z) = e.symm (N.coordinate_map (z.1, (z.2 : ℝ)))
    rw [N.coordinate_map_eq]
  · rintro _ ⟨y, hy, rfl⟩
    change N.coordinate_inverse (e (e.symm y)) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [hright y (hcapture hy)]
    exact N.coordinate_inverse_mem y hy
  · intro z
    have hz := z.2.property
    have hzcarrier : (N.coordinate z : X) ∈ N.carrier := (N.coordinate z).property
    rw [Homeomorph.trans_apply]
    dsimp [tinv]
    rw [hH_apply, hright _ (hcapture hzcarrier), N.coordinate_map_eq z]
    exact N.coordinate_inverse_coordinate_map_of_axial (z.1, (z.2 : ℝ)) hz
  · rintro _ ⟨y, hy, rfl⟩
    have hyT := hcapture hy
    have hyinv : e (e.symm y) = y := e.right_inv hyT
    have hw : e (e.symm y) ∈ N.carrier := by
      rw [hyinv]
      exact hy
    have hcoord := N.coordinate_inverse_right (e (e.symm y)) hw
    have hval : (N.coordinate
        ((N.coordinate_inverse (e (e.symm y))).1,
          ⟨(N.coordinate_inverse (e (e.symm y))).2,
            (N.coordinate_inverse_mem (e (e.symm y)) hw).2⟩) : X) = e (e.symm y) :=
      congrArg Subtype.val hcoord
    have hleft : e.symm (e (e.symm y)) = e.symm y := e.left_inv (e.map_target hyT)
    rw [Homeomorph.trans_apply]
    dsimp [tinv]
    apply Subtype.ext
    rw [hH_apply, hval, hleft]
  · rw [N.central_sphere_eq, image_image]
  · exact ⟨N.center, N.center_on_central_sphere, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, N.central_sphere_subset hy, rfl⟩

@[simp] theorem pullbackNeckGeometry_center
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (D : LeviCivitaData g)
    (hscalar : 0 < D.scalarCurvature (e.symm N.center)) :
    (pullbackNeckGeometry e N hcapture D hscalar).center = e.symm N.center := rfl

@[simp] theorem pullbackNeckGeometry_coordinate_map
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (D : LeviCivitaData g)
    (hscalar : 0 < D.scalarCurvature (e.symm N.center)) (z : UnitTwoSphere × ℝ) :
    (pullbackNeckGeometry e N hcapture D hscalar).coordinate_map z =
      e.symm (N.coordinate_map z) := rfl

@[simp] theorem pullbackNeckGeometry_carrier
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (D : LeviCivitaData g)
    (hscalar : 0 < D.scalarCurvature (e.symm N.center)) :
    (pullbackNeckGeometry e N hcapture D hscalar).carrier = e.symm '' N.carrier := rfl

@[simp] theorem pullbackNeckGeometry_scale
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (D : LeviCivitaData g)
    (hscalar : 0 < D.scalarCurvature (e.symm N.center)) :
    (pullbackNeckGeometry e N hcapture D hscalar).scale =
      (D.scalarCurvature (e.symm N.center)) ^ (-1 / 2 : ℝ) := rfl

end PoincareConjecture.Proofs.M28.NeckTransfer
