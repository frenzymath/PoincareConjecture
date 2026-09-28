import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CapCore
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.ContainedCollar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem exists_boundary_diffeomorph_of_ball_neighborhood
    (b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M)
    (hs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hboundary : b '' Metric.sphere 0 1 = C.boundary_sphere) :
    ∃ d : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      ∀ p : UnitTwoSphere, b (d p) = C.boundary_neck.coordinate_map (p, 0) := by
  let N := C.boundary_neck
  have hzero (p : UnitTwoSphere) : (p, (0 : ℝ)) ∈ N.cylinderDomain :=
    ⟨mem_univ _, neg_neg_of_pos (inv_pos.mpr N.epsilon_pos),
      inv_pos.mpr N.epsilon_pos⟩
  have hn (p : UnitTwoSphere) : N.coordinate_map (p, 0) ∈ C.boundary_sphere := by
    rw [C.boundary_eq_neck_sphere, ← N.centralSphere_range]
    exact mem_range_self p
  have hbt : C.boundary_sphere ⊆ b.target := by
    rw [← hboundary]
    rintro _ ⟨x, hx, rfl⟩
    exact b.map_source (hs (Metric.sphere_subset_closedBall hx))
  have hbinv (p : UnitTwoSphere) :
      b.symm (N.coordinate_map (p, 0)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    obtain ⟨x, hx, heq⟩ := hboundary.symm ▸ hn p
    rw [← heq, b.left_inv (hs (Metric.sphere_subset_closedBall hx))]
    exact hx
  have hbn (q : UnitTwoSphere) : b q ∈ N.central_sphere := by
    rw [← C.boundary_eq_neck_sphere, ← hboundary]
    exact mem_image_of_mem b q.property
  let f : UnitTwoSphere → UnitTwoSphere :=
    fun p => ⟨b.symm (N.coordinate_map (p, 0)), hbinv p⟩
  let k : UnitTwoSphere → UnitTwoSphere := fun q => (N.coordinate_inverse (b q)).1
  have hbf (p : UnitTwoSphere) : b (f p) = N.coordinate_map (p, 0) :=
    b.right_inv (hbt (hn p))
  have hnk (q : UnitTwoSphere) : N.coordinate_map (k q, 0) = b q := by
    have hq := (N.mem_central_sphere_iff _).mp (hbn q)
    change N.coordinate_map ((N.coordinate_inverse (b q)).1, 0) = b q
    rw [← hq.2]
    exact N.coordinate_map_coordinate_inverse hq.1
  have hkf (p : UnitTwoSphere) : k (f p) = p := by
    change (N.coordinate_inverse (b (f p))).1 = p
    rw [hbf, N.coordinate_inverse_coordinate_map (hzero p)]
  have hfk (q : UnitTwoSphere) : f (k q) = q := by
    apply Subtype.ext
    change b.symm (N.coordinate_map (k q, 0)) = q.val
    rw [hnk, b.left_inv (hs (Metric.sphere_subset_closedBall q.property))]
  have hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f := by
    have h : ContMDiff (𝓡 2) (𝓡 3) ∞
        (fun p : UnitTwoSphere => b.symm (N.coordinate_map (p, 0))) := by
      intro p
      exact (hbi.contMDiffAt (b.open_target.mem_nhds (hbt (hn p)))).comp p
        (N.centralSphere_contMDiff p)
    exact h.codRestrict_sphere (hbinv ·)
  have hk : ContMDiff (𝓡 2) (𝓡 2) ∞ k := by
    intro q
    exact contMDiffAt_fst.comp q
      ((N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (N.central_sphere_subset (hbn q)))).comp q
          ((hb.contMDiffAt (b.open_source.mem_nhds
            (hs (Metric.sphere_subset_closedBall q.property)))).comp q
              (contMDiff_coe_sphere q)))
  exact ⟨{
    toFun := f
    invFun := k
    left_inv := hkf
    right_inv := hfk
    contMDiff_toFun := hf
    contMDiff_invFun := hk }, hbf⟩

theorem exists_ball_coordinate_collar
    (b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M)
    (hs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hboundary : b '' Metric.sphere 0 1 = C.boundary_sphere) :
    ∃ r : ℝ, 0 < r ∧ r < C.epsilon⁻¹ ∧
      ∃ e : OpenPartialHomeomorph RoundCylinderSpace (EuclideanSpace ℝ (Fin 3)),
        univ ×ˢ Ioo (-r) r ⊆ e.source ∧
        e.target ⊆ b.source ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
        e '' (univ ×ˢ ({0} : Set ℝ)) = Metric.sphere 0 1 ∧
        ∀ z ∈ e.source, b (e z) = C.boundary_neck.coordinate_map z := by
  let N := C.boundary_neck
  obtain ⟨d, hd⟩ := C.exists_boundary_diffeomorph_of_ball_neighborhood b hs hb hbi hboundary
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hbt (p : UnitTwoSphere) : N.coordinate_map (p, 0) ∈ b.target := by
    rw [← hd]
    exact b.map_source (hs (Metric.sphere_subset_closedBall (d p).property))
  obtain ⟨a, ha, hcollar⟩ :=
    N.exists_slice_collar_in_open hzero b.target b.open_target hbt
  let r := min a (C.epsilon⁻¹ / 2)
  have hr : 0 < r := lt_min ha (half_pos (inv_pos.mpr C.epsilon_pos))
  let e := N.coordinatePartialHomeomorph.trans b.symm
  have hes : univ ×ˢ Ioo (-r) r ⊆ e.source := by
    intro z hz
    have hzabs : |z.2| < a := (abs_lt.mpr hz.2).trans_le (min_le_left _ _)
    obtain ⟨hdom, ht⟩ := hcollar z.1 z.2 hzabs
    exact ⟨⟨mem_univ _, by simpa using hdom⟩, by simpa using ht⟩
  have hezero (p : UnitTwoSphere) : e (p, 0) = (d p).val := by
    change b.symm (N.coordinate_map (p, 0)) = (d p).val
    rw [← hd, b.left_inv (hs (Metric.sphere_subset_closedBall (d p).property))]
  refine ⟨r, hr, (min_le_right _ _).trans_lt (half_lt_self
    (inv_pos.mpr C.epsilon_pos)), e, hes, inter_subset_left, ?_, ?_, ?_, ?_⟩
  · exact hbi.comp (N.coordinate_map_smooth.mono inter_subset_left) inter_subset_right
  · exact N.coordinate_inverse_smooth.comp (hb.mono inter_subset_left) inter_subset_right
  · ext x
    constructor
    · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, heq⟩
      have ht0 : t = 0 := ht
      subst t
      rw [hezero] at heq
      exact heq ▸ (d p).property
    · intro hx
      refine ⟨(d.symm ⟨x, hx⟩, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      rw [hezero, d.apply_symm_apply]
  · intro z hz
    exact b.right_inv hz.2

theorem ball_coordinate_collar_sides
    (b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M)
    (hs : Metric.closedBall 0 1 ⊆ b.source)
    (hclosed : b '' Metric.closedBall 0 1 = C.closed_core)
    (e : OpenPartialHomeomorph RoundCylinderSpace (EuclideanSpace ℝ (Fin 3)))
    {r : ℝ} (hr : r < C.epsilon⁻¹)
    (hes : univ ×ˢ Ioo (-r) r ⊆ e.source)
    (het : e.target ⊆ b.source)
    (heq : ∀ z ∈ e.source, b (e z) = C.boundary_neck.coordinate_map z) :
    (e '' (univ ×ˢ Ioo (-r) 0) ⊆ Metric.ball 0 1 ∧
      e '' (univ ×ˢ Ioo 0 r) ⊆ (Metric.closedBall 0 1)ᶜ) ∨
    (e '' (univ ×ˢ Ioo 0 r) ⊆ Metric.ball 0 1 ∧
      e '' (univ ×ˢ Ioo (-r) 0) ⊆ (Metric.closedBall 0 1)ᶜ) := by
  let N := C.boundary_neck
  have hopen : b '' Metric.ball 0 1 = C.core := by
    rw [b.image_ball_eq_interior hs hclosed, ← C.core_eq_interior_closed_core]
  have hmap {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-r) r) :
      e z ∈ Metric.ball 0 1 ↔ N.coordinate_map z ∈ C.core := by
    rw [← hopen, ← heq z (hes hz)]
    constructor
    · exact mem_image_of_mem b
    · rintro ⟨x, hx, he⟩
      have hxe := b.injOn (hs (Metric.ball_subset_closedBall hx))
        (het (e.map_source (hes hz))) he
      exact hxe ▸ hx
  have hout {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-r) r)
      (hend : N.coordinate_map z ∈ C.end_neck.carrier) :
      e z ∈ (Metric.closedBall 0 1)ᶜ := by
    intro hx
    have hcore : b (e z) ∈ C.closed_core := hclosed ▸ mem_image_of_mem b hx
    rw [heq z (hes hz)] at hcore
    exact Set.disjoint_left.mp C.disjoint_closed_core_end hcore hend
  have hregion {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-r) r)
      {a c : ℝ} (hac : z.2 ∈ Ioo a c) : N.coordinate_map z ∈ N.region a c := by
    have hdom : z ∈ N.cylinderDomain := by
      refine ⟨mem_univ _, ?_, ?_⟩ <;>
        dsimp [N] <;> rw [C.boundary_neck_epsilon] <;> linarith [hz.2.1, hz.2.2]
    exact ⟨N.coordinate_map_mem hdom, by
      rw [N.coordinate_inverse_coordinate_map hdom]
      exact hac⟩
  have hneg {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-r) 0) :
      z ∈ univ ×ˢ Ioo (-r) r ∧
        N.coordinate_map z ∈ N.region (-N.epsilon⁻¹) 0 := by
    have hz' : z ∈ univ ×ˢ Ioo (-r) r := ⟨hz.1, hz.2.1, by linarith [hz.2.1, hz.2.2]⟩
    refine ⟨hz', hregion hz' ⟨?_, hz.2.2⟩⟩
    dsimp [N]
    rw [C.boundary_neck_epsilon]
    linarith [hz.2.1]
  have hpos {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo 0 r) :
      z ∈ univ ×ˢ Ioo (-r) r ∧
        N.coordinate_map z ∈ N.region 0 N.epsilon⁻¹ := by
    have hz' : z ∈ univ ×ˢ Ioo (-r) r := ⟨hz.1, by linarith [hz.2.1, hz.2.2], hz.2.2⟩
    refine ⟨hz', hregion hz' ⟨hz.2.1, ?_⟩⟩
    dsimp [N]
    rw [C.boundary_neck_epsilon]
    exact hz.2.2.trans hr
  rcases C.boundary_neck_sides with ⟨hn, hp⟩ | ⟨hp, hn⟩
  · left
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact (hmap (hneg hz).1).mpr (hn (hneg hz).2)
    · rintro _ ⟨z, hz, rfl⟩
      exact hout (hpos hz).1 (hp (hpos hz).2)
  · right
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact (hmap (hpos hz).1).mpr (hp (hpos hz).2)
    · rintro _ ⟨z, hz, rfl⟩
      exact hout (hneg hz).1 (hn (hneg hz).2)

theorem exists_euclidean_core_standardization (hkind : C.model_kind = .euclidean) :
    ∃ b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      Metric.closedBall 0 1 ⊆ b.source ∧
      C.closed_core ⊆ b.target ∧
      b.target ⊆ C.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = C.closed_core ∧
      b '' Metric.ball 0 1 = C.core ∧
      b '' Metric.sphere 0 1 = C.boundary_sphere ∧
      ∃ d : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        ∀ p : UnitTwoSphere, b (d p) = C.boundary_neck.coordinate_map (p, 0) := by
  obtain ⟨b, hs, ht, hb, hbi, hclosed, hopen, hboundary⟩ :=
    C.exists_euclidean_closed_core_ball_neighborhood hkind
  let c := (b.symm.restrOpen C.carrier C.carrier_open).symm
  have hcs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ c.source := by
    intro x hx
    exact ⟨hs hx, C.closed_core_subset_carrier (hclosed ▸ mem_image_of_mem b hx)⟩
  have hct : C.closed_core ⊆ c.target := fun x hx =>
    ⟨ht hx, C.closed_core_subset_carrier hx⟩
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c c.source :=
    hb.mono inter_subset_left
  have hci : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    hbi.mono inter_subset_left
  exact ⟨c, hcs, hct, inter_subset_right, hc, hci, hclosed, hopen, hboundary,
    C.exists_boundary_diffeomorph_of_ball_neighborhood c hcs hc hci hboundary⟩

theorem exists_euclidean_core_boundary_filling (hkind : C.model_kind = .euclidean) :
    ∃ b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      Metric.closedBall 0 1 ⊆ b.source ∧
      C.closed_core ⊆ b.target ∧
      b.target ⊆ C.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = C.closed_core ∧
      b '' Metric.ball 0 1 = C.core ∧
      b '' Metric.sphere 0 1 = C.boundary_sphere ∧
      ∀ p : UnitTwoSphere, b p = C.boundary_neck.coordinate_map (p, 0) := by
  obtain ⟨b, hs, ht, hcap, hb, hbi, hclosed, _, _, d, hd⟩ :=
    C.exists_euclidean_core_standardization hkind
  obtain ⟨F, hFball, δ, hδ, _, hF⟩ :=
    Poincare.Manifold.exists_sphere_diffeomorph_extension d
  let c := F.toHomeomorph.toOpenPartialHomeomorph.trans b
  have hcs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ c.source := by
    intro x hx
    exact ⟨mem_univ _, hs (hFball ▸ mem_image_of_mem F hx)⟩
  have hct : c.target = b.target := by
    simp [c]
  have hcimage : c '' Metric.closedBall 0 1 = C.closed_core := by
    change (b ∘ F) '' Metric.closedBall 0 1 = C.closed_core
    calc
      (b ∘ F) '' Metric.closedBall 0 1 = b '' (F '' Metric.closedBall 0 1) :=
        (image_image (⇑b) (⇑F) (Metric.closedBall 0 1)).symm
      _ = C.closed_core := by rw [hFball, hclosed]
  refine ⟨c, hcs, hct.symm ▸ ht, hct.symm ▸ hcap, ?_, ?_, hcimage, ?_, ?_, ?_⟩
  · exact hb.comp F.contMDiff.contMDiffOn inter_subset_right
  · exact F.symm.contMDiff.comp_contMDiffOn (hbi.mono inter_subset_left)
  · rw [c.image_ball_eq_interior hcs hcimage, ← C.core_eq_interior_closed_core]
  · rw [c.image_sphere_eq_frontier hcs hcimage,
      C.closed_core_compact.isClosed.frontier_eq, ← C.core_eq_interior_closed_core,
      ← C.boundary_eq_closed_core_diff_core]
  · intro p
    have hFp : F (p : EuclideanSpace ℝ (Fin 3)) = (d p).val := by
      simpa using hF p 1 (by constructor <;> linarith)
    change b (F p) = _
    rw [hFp, hd]

end PoincareConjecture.CapCertificate
