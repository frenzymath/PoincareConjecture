import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.EmbeddingInverse
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckTransfer
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.SharedExport

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.NeckGeometry

open PoincareConjecture.Proofs.M28.NeckTransfer

noncomputable def captured_source_neck_geometry
    {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A) (j : ℕ)
    (N : EpsilonNeck (g (G.subsequence j)))
    (hcapture : N.carrier ⊆ G.embedding j '' G.exhaustion j)
    (D : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      LeviCivitaData G.limitMetric)
    (hscalar : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      0 < D.scalarCurvature (stageInverse G j N.center))
    (hscale : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      N.scale = (D.scalarCurvature (stageInverse G j N.center)) ^
        (-1 / 2 : ℝ)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    NeckGeometryCore G.limitMetric N.epsilon := by
  classical
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 3) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let e := stageDiffeomorph G j
  let V : Set G.limitCarrier.carrier := e.symm '' N.carrier
  have hcapTarget : N.carrier ⊆ e.target := by
    intro x hx
    change x ∈ G.embedding j '' G.exhaustion j
    exact hcapture hx
  have hVopen : IsOpen V := by
    exact e.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target
      N.carrier_open hcapTarget
  let H := e.toOpenPartialHomeomorph.symm.homeomorphOfImageSubsetSource
    hcapTarget (rfl : e.symm '' N.carrier = V)
  have hH_apply (y : N.carrier) :
      (H y : G.limitCarrier.carrier) = e.symm y := by
    rfl
  let tmap : UnitTwoSphere × ℝ → G.limitCarrier.carrier :=
    fun z => e.symm (N.coordinate_map z)
  let tinv : G.limitCarrier.carrier → UnitTwoSphere × ℝ :=
    fun x => N.coordinate_inverse (e x)
  have hcoord_mem : ∀ z : UnitTwoSphere × ℝ,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map z ∈ e.target := by
    intro z hz
    exact hcapTarget (N.coordinate_map_mem_of_axial z hz)
  have hVsource : V ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hcapTarget hy)
  have hmap_to_carrier : ∀ x ∈ V, e x ∈ N.carrier := by
    rintro x ⟨y, hy, rfl⟩
    have heq : e (e.symm y) = y := e.right_inv (hcapTarget hy)
    change e (e.symm y) ∈ N.carrier
    rw [heq]
    exact hy
  have hcoord_smooth :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ tmap
        (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
    exact e.contMDiffOn_invFun.comp N.coordinate_map_smooth
      (fun z hz => hcoord_mem z hz.2)
  have hinv_smooth :
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ tinv V := by
    exact N.coordinate_inverse_smooth.comp
      (e.contMDiffOn_toFun.mono hVsource) hmap_to_carrier
  have hNcenter : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hcenter_target : N.center ∈ e.target := hcapTarget hNcenter
  refine {
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := N.scale
    scale_pos := N.scale_pos
    center := e.symm N.center
    connection := D
    scalar_center_pos := hscalar
    scale_eq_scalar := hscale
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
    change e.symm (N.coordinate z) =
      e.symm (N.coordinate_map (z.1, (z.2 : ℝ)))
    rw [N.coordinate_map_eq]
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyT := hcapTarget hy
    have heq : e (e.symm y) = y := e.right_inv hyT
    change N.coordinate_inverse (e (e.symm y)) ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [heq]
    exact N.coordinate_inverse_mem y hy
  · intro z
    have hz := z.2.property
    have hzcarrier : (N.coordinate z : M (G.subsequence j)) ∈ N.carrier :=
      (N.coordinate z).property
    rw [Homeomorph.trans_apply]
    dsimp [tinv]
    rw [hH_apply]
    have heq : e (e.symm (N.coordinate z)) = (N.coordinate z) :=
      e.right_inv (hcapTarget hzcarrier)
    rw [heq]
    rw [N.coordinate_map_eq z]
    exact N.coordinate_inverse_coordinate_map_of_axial (z.1, (z.2 : ℝ)) hz
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hyT := hcapTarget hy
    have hyinv : e (e.symm y) = y := e.right_inv hyT
    have hycoord := N.coordinate_inverse_mem y hy
    have hw : e (e.symm y) ∈ N.carrier := by
      rw [hyinv]
      exact hy
    have hcoord : N.coordinate
        ((N.coordinate_inverse (e (e.symm y))).1,
          ⟨(N.coordinate_inverse (e (e.symm y))).2,
            (N.coordinate_inverse_mem (e (e.symm y)) hw).2⟩) =
        ⟨e (e.symm y), hw⟩ :=
      N.coordinate_inverse_right _ hw
    have hval : (N.coordinate
        ((N.coordinate_inverse (e (e.symm y))).1,
          ⟨(N.coordinate_inverse (e (e.symm y))).2,
            (N.coordinate_inverse_mem (e (e.symm y)) hw).2⟩) :
        M (G.subsequence j)) = e (e.symm y) :=
      congrArg Subtype.val hcoord
    have hsrc : e.symm y ∈ e.source := e.map_target hyT
    have hleft : e.symm (e (e.symm y)) = e.symm y := e.left_inv hsrc
    rw [Homeomorph.trans_apply]
    dsimp [tinv]
    apply Subtype.ext
    rw [hH_apply]
    rw [hval, hleft]
  · rw [N.central_sphere_eq, image_image]
  · exact ⟨N.center, N.center_on_central_sphere, rfl⟩
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, N.central_sphere_subset hy, rfl⟩

noncomputable def captured_source_neck_geometry_of_window
    {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A : ℝ}
    (E : PartialLimitWindowExport F p A) (j : ℕ)
    (N : EpsilonNeck ((F (E.limit.subsequence j)).metric 0))
    (hcapture : N.carrier ⊆
      E.limit.embedding j '' E.limit.exhaustion j)
    (D : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      LeviCivitaData E.limit.limitMetric)
    (hscalar : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      0 < D.scalarCurvature
        (stageInverse E.limit.toPartialPointedMetricConvergence j N.center))
    (hscale : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      N.scale = (D.scalarCurvature
        (stageInverse E.limit.toPartialPointedMetricConvergence j N.center)) ^
          (-1 / 2 : ℝ)) :
    letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    NeckGeometryCore E.limit.limitMetric N.epsilon := by
  exact captured_source_neck_geometry
    (g := fun k => (F k).metric 0) (p := p) (A := A)
    E.limit.toPartialPointedMetricConvergence j N hcapture D hscalar hscale

end PoincareConjecture.M28.NeckGeometry
