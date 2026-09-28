import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ModelCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollaredDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine












noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)



theorem closure_exterior_eq_component_diff_core :
    closure (connectedComponent C.boundary_neck.center \ C.closed_core) =
      connectedComponent C.boundary_neck.center \ C.core := by
  rw [closure_eq_self_union_frontier, C.frontier_exterior_eq_boundary,
    C.boundary_eq_closed_core_diff_core]
  have hsub := C.closed_core_subset_carrier.trans C.carrier_subset_boundary_component
  ext x
  have h₁ := hsub (a := x)
  have h₂ := C.core_subset_closed_core (a := x)
  simp only [mem_union, mem_sdiff]
  tauto



theorem interior_closure_exterior :
    interior (closure (connectedComponent C.boundary_neck.center \ C.closed_core)) =
      connectedComponent C.boundary_neck.center \ C.closed_core := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E3 M
  rw [C.closure_exterior_eq_component_diff_core, sdiff_eq, interior_inter,
    isOpen_connectedComponent.interior_eq, interior_compl,
    C.closure_core_eq_closed_core]
  rfl



theorem exists_ball_neighborhood_of_exterior_in_euclidean_cap (D : CapCertificate g)
    (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact
      (closure (connectedComponent C.boundary_neck.center \ C.closed_core)))
    (hsub : closure (connectedComponent C.boundary_neck.center \ C.closed_core) ⊆
      D.carrier) :
    ∃ b : OpenPartialHomeomorph E3 M,
      Metric.closedBall 0 1 ⊆ b.source ∧ b.target ⊆ D.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 =
        closure (connectedComponent C.boundary_neck.center \ C.closed_core) ∧
      b '' Metric.ball 0 1 = connectedComponent C.boundary_neck.center \ C.closed_core ∧
      b '' Metric.sphere 0 1 = C.boundary_sphere := by
  let A := connectedComponent C.boundary_neck.center \ C.closed_core
  let L := closure A
  have hLi : interior L = A := C.interior_closure_exterior
  have hLregular : closure (interior L) = L := by rw [hLi]
  have hLf : frontier L = C.boundary_sphere := by
    rw [frontier, isClosed_closure.closure_eq, hLi]
    exact (C.isOpen_component_diff_closed_core.frontier_eq).symm.trans
      C.frontier_exterior_eq_boundary
  obtain ⟨e, hes, het, he, hei⟩ := D.exists_euclidean_coordinates hD
  let K := e '' L
  have hLs : L ⊆ e.source := hes.symm ▸ hsub
  have hK : IsCompact K := hcompact.image_of_continuousOn (e.continuousOn.mono hLs)
  have himage : e.IsImage L K := e.isImage_image_of_subset_source hLs
  have hKi : interior K = e '' interior L := by
    have h := himage.interior.image_eq
    rw [inter_eq_right.mpr (interior_subset.trans hLs), het, univ_inter] at h
    exact h.symm
  have hKregular : closure (interior K) = K := by
    rw [hKi]
    obtain ⟨_, _, hclosure, _⟩ := e.image_region_of_isCompact_closure
      isOpen_interior (hLregular.symm ▸ hcompact) (hLregular.symm ▸ hLs)
    simpa only [hLregular] using hclosure
  have hKf : frontier K = e '' C.boundary_sphere := by
    have h := himage.frontier.image_eq
    rw [inter_eq_right.mpr (hcompact.isClosed.frontier_subset.trans hLs), het,
      univ_inter, hLf] at h
    exact h.symm
  let N := C.boundary_neck
  let j := N.coordinatePartialHomeomorph.trans e
  have hj : ContMDiffOn CylModel (𝓡 3) ∞ j j.source :=
    he.comp (N.coordinate_map_smooth.mono inter_subset_left) inter_subset_right
  have hji : ContMDiffOn (𝓡 3) CylModel ∞ j.symm j.target :=
    N.coordinate_inverse_smooth.comp (hei.mono inter_subset_left) inter_subset_right
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ j.source := by
    refine ⟨⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
      inv_pos.mpr N.epsilon_pos⟩, ?_⟩
    apply hLs
    apply frontier_subset_closure
    rw [C.frontier_exterior_eq_boundary, C.boundary_eq_neck_sphere,
      ← N.centralSphere_range]
    exact mem_range_self q
  obtain ⟨δ, hδ, hδj⟩ := CylinderGluing.exists_cylinder_collar
    ⟨j.source, j.open_source⟩ hzero
  have hjs : univ ×ˢ Ioo (-δ) δ ⊆ j.source :=
    fun z hz => hδj z (abs_lt.mpr hz.2)
  have hfront : frontier K = range (fun q : UnitTwoSphere => j (q, 0)) := by
    rw [hKf, C.boundary_eq_neck_sphere, ← N.centralSphere_range, ← range_comp]
    rfl
  have hcoord (y : E3) (hy : y ∈ j.target) :
      N.coordinate_map (j.symm y) = e.symm y :=
    N.coordinatePartialHomeomorph.right_inv hy.2
  have hheight (y : E3) (hy : y ∈ j.target) :
      (j.symm y).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (j.map_target hy).1.2
  have hmem (y : E3) (hy : y ∈ j.target) : y ∈ K ↔ e.symm y ∉ C.core := by
    rw [← himage.symm_apply_mem_iff hy.1]
    change e.symm y ∈ closure (connectedComponent C.boundary_neck.center \ C.closed_core) ↔ _
    rw [C.closure_exterior_eq_component_diff_core]
    exact and_iff_right (C.carrier_subset_boundary_component (C.boundary_neck_subset hy.2))
  have hzK (y : E3) (hy : y ∈ j.target) (hz : (j.symm y).2 = 0) : y ∈ K := by
    apply (hmem y hy).mpr
    have hboundary : e.symm y ∈ C.boundary_sphere := by
      rw [C.boundary_eq_neck_sphere, ← N.centralSphere_range, ← hcoord y hy]
      exact ⟨(j.symm y).1, by rw [← hz]⟩
    exact fun hx => disjoint_left.mp C.disjoint_core_boundary hx hboundary
  have hregion (y : E3) (hy : y ∈ j.target) {a b : ℝ}
      (ht : (j.symm y).2 ∈ Ioo a b) : e.symm y ∈ N.region a b := by
    exact ⟨hy.2, ht⟩
  have hfill
      (c : OpenPartialHomeomorph RoundCylinderSpace E3)
      (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
      (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
      (hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
      (hcf : frontier K = range (fun q : UnitTwoSphere => c (q, 0)))
      (hside : ∀ y ∈ c.target, y ∈ K ↔ 0 ≤ (c.symm y).2) :
      ∃ b : OpenPartialHomeomorph E3 M,
        Metric.closedBall 0 1 ⊆ b.source ∧ b.target ⊆ D.carrier ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
        b '' Metric.closedBall 0 1 = L ∧ b '' Metric.ball 0 1 = A ∧
        b '' Metric.sphere 0 1 = C.boundary_sphere := by
    obtain ⟨f, hfs, _, hf, hfi, hfK⟩ :=
      Poincare.Manifold.Schoenflies.ball_neighborhood_of_compact_collar_side
        hK hKregular c hc hci hδ hcs hcf hside
    let b := f.trans e.symm
    have hbs : Metric.closedBall (0 : E3) 1 ⊆ b.source := by
      intro x hx
      refine ⟨hfs hx, ?_⟩
      change f x ∈ e.target
      rw [het]
      exact mem_univ _
    have hbL : b '' Metric.closedBall 0 1 = L := by
      change (e.symm ∘ f) '' Metric.closedBall 0 1 = L
      rw [image_comp, hfK]
      exact e.toPartialEquiv.symm_image_image_of_subset_source hLs
    refine ⟨b, hbs, fun y hy => hes ▸ hy.1,
      hei.comp (hf.mono inter_subset_left) inter_subset_right,
      hfi.comp (he.mono inter_subset_left) inter_subset_right, hbL, ?_, ?_⟩
    · rw [b.image_ball_eq_interior hbs hbL, hLi]
    · rw [b.image_sphere_eq_frontier hbs hbL, hLf]
  rcases C.boundary_neck_sides with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · apply hfill j hj hji hjs hfront
    intro y hy
    constructor
    · intro hyK
      by_contra ht
      exact (hmem y hy).mp hyK (hin (hregion y hy ⟨(hheight y hy).1, lt_of_not_ge ht⟩))
    · intro ht
      rcases lt_or_eq_of_le ht with ht | ht
      · apply (hmem y hy).mpr
        exact fun hx => disjoint_left.mp C.disjoint_closed_core_end
          (C.core_subset_closed_core hx) (hout (hregion y hy ⟨ht, (hheight y hy).2⟩))
      · exact hzK y hy ht.symm
  · let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
      toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
      contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
      contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
    let c := R.toHomeomorph.toOpenPartialHomeomorph.trans j
    have hct : c.target = j.target := by simp [c]
    apply hfill c (hj.comp R.contMDiff.contMDiffOn inter_subset_right)
      (R.symm.contMDiff.comp_contMDiffOn (hji.mono inter_subset_left))
    · intro z hz
      refine ⟨mem_univ _, hjs ?_⟩
      change (z.1, -z.2) ∈ univ ×ˢ Ioo (-δ) δ
      exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    · convert hfront using 1
      congr 1
      funext q
      change j (q, -(0 : ℝ)) = j (q, 0)
      rw [neg_zero]
    · intro y hy
      have hyj : y ∈ j.target := hct ▸ hy
      change y ∈ K ↔ 0 ≤ -(j.symm y).2
      rw [neg_nonneg]
      constructor
      · intro hyK
        by_contra ht
        exact (hmem y hyj).mp hyK
          (hin (hregion y hyj ⟨lt_of_not_ge ht, (hheight y hyj).2⟩))
      · intro ht
        rcases lt_or_eq_of_le ht with ht | ht
        · apply (hmem y hyj).mpr
          exact fun hx => disjoint_left.mp C.disjoint_closed_core_end
            (C.core_subset_closed_core hx) (hout (hregion y hyj ⟨(hheight y hyj).1, ht⟩))
        · exact hzK y hyj ht

end PoincareConjecture.CapCertificate
