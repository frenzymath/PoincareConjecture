import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.MarkedBallFlattening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.BallBoundaryChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BoundedSide

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Rounding.CommonDisk

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_boundary_patch
    (a : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f : E2 → S2) {x : E2} (hx : x ∈ ball 0 1)
    (hfl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x) :
    ∃ W : Set E3, IsOpen W ∧ a (f x) ∈ W ∧
      W ∩ (a '' sphere 0 1) ⊆ (fun y => a (f y)) '' ball (0 : E2) 1 := by
  obtain ⟨e, hxe, heq⟩ := hfl
  let V := e.toOpenPartialHomeomorph '' (e.source ∩ ball (0 : E2) 1)
  have hVo : IsOpen V :=
    e.toOpenPartialHomeomorph.isOpen_image_source_inter isOpen_ball
  obtain ⟨T, hTo, hT⟩ :=
    (Topology.IsInducing.isOpen_iff (f := (Subtype.val : S2 → E3))
      Topology.IsEmbedding.subtypeVal.isInducing).mp hVo
  have hfx : (f x : E3) ∈ T := by
    change f x ∈ Subtype.val ⁻¹' T
    rw [hT]
    exact ⟨x, ⟨hxe, hx⟩, (heq hxe).symm⟩
  refine ⟨a '' T, a.toHomeomorph.isOpenMap T hTo, mem_image_of_mem a hfx, ?_⟩
  rintro z ⟨⟨y, hyT, hyz⟩, ⟨w, hw, hwz⟩⟩
  have hwy : w = y := a.injective (hwz.trans hyz.symm)
  subst w
  have hyV : (⟨y, hw⟩ : S2) ∈ V := by
    rw [← hT]
    exact hyT
  obtain ⟨t, ⟨hte, ht⟩, het⟩ := hyV
  refine ⟨t, ht, ?_⟩
  have hft : (f t : E3) = y := congrArg Subtype.val ((heq hte).trans het)
  change a (f t) = z
  rw [hft, hyz]

theorem exists_boundary_coincidence
    (a b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f g : E2 → S2) {x : E2} (hx : x ∈ ball 0 1)
    (hfl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x)
    (hgl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (hag : ∀ y ∈ closedBall (0 : E2) 1, a (f y) = b (g y)) :
    ∃ W : Set E3, IsOpen W ∧ a (f x) ∈ W ∧
      W ∩ (a '' sphere 0 1) = W ∩ (b '' sphere 0 1) ∧
      W ∩ (a '' sphere 0 1) ⊆ (fun y => a (f y)) '' ball (0 : E2) 1 := by
  obtain ⟨V, hVo, hxV, hV⟩ := exists_boundary_patch a f hx hfl
  obtain ⟨T, hTo, hxT, hT⟩ := exists_boundary_patch b g hx hgl
  refine ⟨V ∩ T, hVo.inter hTo,
    ⟨hxV, hag x (ball_subset_closedBall hx) ▸ hxT⟩, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro z ⟨hzW, hzA⟩
      obtain ⟨y, hy, rfl⟩ := hV ⟨hzW.1, hzA⟩
      refine ⟨hzW, ?_⟩
      change a (f y) ∈ b '' sphere 0 1
      rw [hag y (ball_subset_closedBall hy)]
      exact mem_image_of_mem b (g y).property
    · rintro z ⟨hzW, hzB⟩
      obtain ⟨y, hy, rfl⟩ := hT ⟨hzW.2, hzB⟩
      refine ⟨hzW, ?_⟩
      change b (g y) ∈ a '' sphere 0 1
      rw [← hag y (ball_subset_closedBall hy)]
      exact mem_image_of_mem a (f y).property
  · rintro z ⟨hzW, hzA⟩
    exact hV ⟨hzW.1, hzA⟩

theorem exists_filled_coincidence_of_subset
    (a b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f g : E2 → S2) {x : E2} (hx : x ∈ ball 0 1)
    (hfl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x)
    (hgl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (hag : ∀ y ∈ closedBall (0 : E2) 1, a (f y) = b (g y))
    (hsub : b '' closedBall 0 1 ⊆ a '' closedBall 0 1) :
    ∃ W : Set E3, IsOpen W ∧ a (f x) ∈ W ∧
      W ∩ (a '' closedBall 0 1) = W ∩ (b '' closedBall 0 1) := by
  obtain ⟨W, hWo, hpW, hboundary, _⟩ :=
    exists_boundary_coincidence a b f g hx hfl hgl hag
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp
    (hWo.preimage a.continuous) (f x) hpW
  let V := a '' ball (f x : E3) r
  have hVo : IsOpen V := a.toHomeomorph.isOpenMap _ isOpen_ball
  have hpV : a (f x) ∈ V := mem_image_of_mem a (mem_ball_self hr)
  have hVW : V ⊆ W := by
    rintro z ⟨y, hy, rfl⟩
    exact hrW hy
  have hcl (c : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
      closure (c '' ball (0 : E3) 1) = c '' closedBall 0 1 := by
    change closure (c.toHomeomorph '' ball (0 : E3) 1) = _
    rw [← c.toHomeomorph.image_closure, closure_ball (0 : E3) one_ne_zero]
    rfl
  have hinner : b '' ball (0 : E3) 1 ⊆ a '' ball 0 1 := by
    have h := interior_mono hsub
    change interior (b.toHomeomorph '' closedBall (0 : E3) 1) ⊆
      interior (a.toHomeomorph '' closedBall (0 : E3) 1) at h
    rw [← b.toHomeomorph.image_interior, ← a.toHomeomorph.image_interior,
      interior_closedBall (0 : E3) one_ne_zero] at h
    exact h
  have hconn : IsPreconnected (V ∩ (a '' ball (0 : E3) 1)) := by
    change IsPreconnected ((a '' ball (f x : E3) r) ∩ (a '' ball (0 : E3) 1))
    rw [← image_inter (show Function.Injective a from a.injective)]
    exact ((convex_ball (f x : E3) r).inter (convex_ball (0 : E3) 1)).isPreconnected.image
      a a.continuous.continuousOn
  have havoid : Disjoint (V ∩ (a '' ball (0 : E3) 1))
      (frontier (b '' ball (0 : E3) 1)) := by
    apply disjoint_left.mpr
    intro z hz hzb
    change z ∈ frontier (b.toHomeomorph '' ball (0 : E3) 1) at hzb
    rw [← b.toHomeomorph.image_frontier, frontier_ball (0 : E3) one_ne_zero] at hzb
    have hza : z ∈ a '' sphere (0 : E3) 1 :=
      (hboundary.symm ▸ (show z ∈ W ∩ (b '' sphere 0 1) from ⟨hVW hz.1, hzb⟩)).2
    obtain ⟨y, hy, rfl⟩ := hz.2
    obtain ⟨w, hw, hwy⟩ := hza
    have hwy' : w = y := a.injective hwy
    subst w
    exact (ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hw)
  have hpcl : a (f x) ∈ closure (b '' ball (0 : E3) 1) := by
    rw [hcl b, hag x (ball_subset_closedBall hx)]
    exact mem_image_of_mem b (sphere_subset_closedBall (g x).property)
  obtain ⟨z, hzV, hzb⟩ := mem_closure_iff.mp hpcl V hVo hpV
  have hcap : V ∩ (a '' ball (0 : E3) 1) ⊆ b '' ball 0 1 :=
    Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
      (b.toHomeomorph.isOpenMap _ isOpen_ball) hconn havoid
      ⟨z, ⟨hzV, hinner hzb⟩, hzb⟩
  refine ⟨V, hVo, hpV, Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hz.1, ?_⟩
    have hza : z ∈ V ∩ closure (a '' ball (0 : E3) 1) := by
      rw [hcl a]
      exact hz
    have hzb := closure_mono hcap (hVo.inter_closure hza)
    rwa [hcl b] at hzb
  · intro z hz
    exact ⟨hz.1, hsub hz.2⟩

theorem exists_preconnected_exterior_neighborhood
    (a : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (v : S2) {W : Set E3} (hWo : IsOpen W) (hvW : a v ∈ W) :
    ∃ V : Set E3, IsOpen V ∧ a v ∈ V ∧ V ⊆ W ∧
      IsPreconnected (V ∩ (a '' closedBall (0 : E3) 1)ᶜ) := by
  let hv : ‖(v : E3)‖ = 1 := norm_eq_of_mem_sphere v
  let q : Hemisphere.Plane (v : E3) × Real → E3 :=
    fun z => a ((unitBallBoundaryChart hv).symm z)
  have hqc : Continuous q := a.continuous.comp
    (continuous_subtype_val.comp (unitBallBoundaryChart hv).symm.continuous)
  have hqo : IsOpenMap q := a.toHomeomorph.isOpenMap.comp
    ((unitBallBoundaryHalfSpace (v : E3)).isOpen.isOpenMap_subtype_val.comp
      (unitBallBoundaryChart hv).symm.toHomeomorph.isOpenMap)
  have hqzero : q 0 = a v := by
    simp [q, unitBallBoundaryChart_symm_apply, Hemisphere.toSphere, hv]
  have hqext (z : Hemisphere.Plane (v : E3) × Real) :
      q z ∈ (a '' closedBall (0 : E3) 1)ᶜ ↔ 0 < z.2 := by
    constructor
    · intro hz
      by_contra h
      apply hz
      refine ⟨((unitBallBoundaryChart hv).symm z : E3), ?_, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, norm_unitBallBoundaryChart_symm] using
        Real.exp_le_one_iff.mpr (le_of_not_gt h)
    · intro hz hmem
      obtain ⟨y, hy, heq⟩ := hmem
      have hyq : y = ((unitBallBoundaryChart hv).symm z : E3) := a.injective heq
      subst y
      have hn : Real.exp z.2 ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right, norm_unitBallBoundaryChart_symm] using hy
      exact (not_le_of_gt hz) (Real.exp_le_one_iff.mp hn)
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp (hWo.preimage hqc) 0
    (show q 0 ∈ W from hqzero ▸ hvW)
  refine ⟨q '' ball 0 r, hqo _ isOpen_ball, ?_, ?_, ?_⟩
  · rw [← hqzero]
    exact mem_image_of_mem q (mem_ball_self hr)
  · rintro y ⟨z, hz, rfl⟩
    exact hrW hz
  · have heq : (q '' ball 0 r) ∩ (a '' closedBall (0 : E3) 1)ᶜ =
        q '' (ball 0 r ∩ {z | 0 < z.2}) := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hze⟩
        exact ⟨z, ⟨hz, (hqext z).mp hze⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hze⟩, rfl⟩
        exact ⟨mem_image_of_mem q hz, (hqext z).mpr hze⟩
    rw [heq]
    have hhalf : Convex Real {z : Hemisphere.Plane (v : E3) × Real | 0 < z.2} :=
      (convex_Ioi (0 : Real)).linear_preimage (LinearMap.snd Real _ _)
    exact ((convex_ball (0 : Hemisphere.Plane (v : E3) × Real) r).inter hhalf).isPreconnected.image
      q hqc.continuousOn

theorem exists_opposite_filled_sides
    (a b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f g : E2 → S2) {x : E2} (hx : x ∈ ball 0 1)
    (hfl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x)
    (hgl : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (hag : ∀ y ∈ closedBall (0 : E2) 1, a (f y) = b (g y))
    (hmeet : (a '' closedBall 0 1) ∩ (b '' closedBall 0 1) =
      (fun y => a (f y)) '' closedBall (0 : E2) 1) :
    ∃ W : Set E3, IsOpen W ∧ a (f x) ∈ W ∧
      W ∩ (a '' closedBall 0 1) = W ∩ (b '' ball 0 1)ᶜ := by
  obtain ⟨W, hWo, hpW, hboundary, _⟩ :=
    exists_boundary_coincidence a b f g hx hfl hgl hag
  obtain ⟨V, hVo, hpV, hVW, hconn⟩ := exists_preconnected_exterior_neighborhood b (g x)
    hWo (hag x (ball_subset_closedBall hx) ▸ hpW)
  have hpV' : a (f x) ∈ V := hag x (ball_subset_closedBall hx) ▸ hpV
  have hAext : a '' ball (0 : E3) 1 ⊆ (b '' closedBall 0 1)ᶜ := by
    rintro z ⟨u, hu, rfl⟩ hzb
    have hzD : a u ∈ (fun y => a (f y)) '' closedBall (0 : E2) 1 :=
      hmeet ▸ (show a u ∈ (a '' closedBall 0 1) ∩ (b '' closedBall 0 1) from
        ⟨mem_image_of_mem a (ball_subset_closedBall hu), hzb⟩)
    obtain ⟨y, _, hfy⟩ := hzD
    have hfu : (f y : E3) = u := a.injective hfy
    have huS : u ∈ sphere (0 : E3) 1 := hfu ▸ (f y).property
    exact (ne_of_lt (mem_ball_zero_iff.mp hu)) (mem_sphere_zero_iff_norm.mp huS)
  have hAclosedExt : a '' closedBall (0 : E3) 1 ⊆ (b '' ball 0 1)ᶜ := by
    intro z hza hzb
    obtain ⟨u, hu, rfl⟩ := hzb
    have hzD : b u ∈ (fun y => a (f y)) '' closedBall (0 : E2) 1 :=
      hmeet ▸ (show b u ∈ (a '' closedBall 0 1) ∩ (b '' closedBall 0 1) from
        ⟨hza, mem_image_of_mem b (ball_subset_closedBall hu)⟩)
    obtain ⟨y, hy, hfy⟩ := hzD
    change a (f y) = b u at hfy
    rw [hag y hy] at hfy
    have hgu : (g y : E3) = u := b.injective hfy
    have huS : u ∈ sphere (0 : E3) 1 := hgu ▸ (g y).property
    exact (ne_of_lt (mem_ball_zero_iff.mp hu)) (mem_sphere_zero_iff_norm.mp huS)
  have havoid : Disjoint (V ∩ (b '' closedBall (0 : E3) 1)ᶜ)
      (frontier (a '' ball (0 : E3) 1)) := by
    apply disjoint_left.mpr
    intro z hz hza
    change z ∈ frontier (a.toHomeomorph '' ball (0 : E3) 1) at hza
    rw [← a.toHomeomorph.image_frontier, frontier_ball (0 : E3) one_ne_zero] at hza
    have hzb : z ∈ b '' sphere (0 : E3) 1 :=
      (hboundary ▸ (show z ∈ W ∩ (a '' sphere 0 1) from ⟨hVW hz.1, hza⟩)).2
    exact hz.2 ((image_mono sphere_subset_closedBall) hzb)
  have hcl : closure (a '' ball (0 : E3) 1) = a '' closedBall 0 1 := by
    change closure (a.toHomeomorph '' ball (0 : E3) 1) = _
    rw [← a.toHomeomorph.image_closure, closure_ball (0 : E3) one_ne_zero]
    rfl
  have hpcl : a (f x) ∈ closure (a '' ball (0 : E3) 1) := by
    rw [hcl]
    exact mem_image_of_mem a (sphere_subset_closedBall (f x).property)
  obtain ⟨z, hzV, hza⟩ := mem_closure_iff.mp hpcl V hVo hpV'
  have hcap : V ∩ (b '' closedBall (0 : E3) 1)ᶜ ⊆ a '' ball 0 1 :=
    Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
      (a.toHomeomorph.isOpenMap _ isOpen_ball) hconn havoid
      ⟨z, ⟨hzV, hAext hza⟩, hza⟩
  have hclExt : closure (b '' closedBall (0 : E3) 1)ᶜ = (b '' ball 0 1)ᶜ := by
    rw [closure_compl]
    change (interior (b.toHomeomorph '' closedBall (0 : E3) 1))ᶜ = _
    rw [← b.toHomeomorph.image_interior, interior_closedBall (0 : E3) one_ne_zero]
    rfl
  refine ⟨V, hVo, hpV', Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨hz.1, hAclosedExt hz.2⟩
  · intro z hz
    refine ⟨hz.1, ?_⟩
    have hzb : z ∈ V ∩ closure (b '' closedBall (0 : E3) 1)ᶜ := by
      rw [hclExt]
      exact hz
    have hza := closure_mono hcap (hVo.inter_closure hzb)
    rwa [hcl] at hza

end Poincare.Manifold.Schoenflies.Rounding.CommonDisk
