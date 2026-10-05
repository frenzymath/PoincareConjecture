import PoincareLib.Topology.Manifold.Surgery.Event.Surgery.SurgeryBallNeighborhood

/-!
# Descending the exact filled ball through a finite smooth cover

The nontrivial fiber transformations separate the full chart after its
outer annulus has been shortened. Local inverse charts then produce the
inverse of the descended ball. The original closedBall and its image are
preserved; no covering-space classification or sphere filling is assumed
to follow from local invertibility alone.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}}

/-- On an injective local diffeomorphism's ball image, its unique inverse
agrees near each point with the corresponding supplied smooth local inverse. -/
theorem ball_local_inverse_smooth (f : StandardCapSpace → A.carrier)
    (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2))
    (hinj : Set.InjOn f (Metric.ball 0 2)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Function.invFunOn f (Metric.ball 0 2))
      (f '' Metric.ball 0 2) := by
  rintro y ⟨x, hx, hxy⟩
  let hlocal := hf ⟨x, hx⟩
  let s := hlocal.localInverse
  have hy : y ∈ s.source := hxy ▸ hlocal.localInverse_mem_source
  have hsy : s y = x := by
    rw [← hxy]
    exact hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ s y :=
    hlocal.contmdiffOn_localInverse.contMDiffAt (s.open_source.mem_nhds hy)
  have hsd : s y ∈ Metric.ball (0 : StandardCapSpace) 2 := hsy ▸ hx
  have hn : ∀ᶠ z in 𝓝 y, s z ∈ Metric.ball (0 : StandardCapSpace) 2 :=
    hs.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hsd)
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [s.open_source.mem_nhds hy, hn] with z hz hsz
  have hzimage : z ∈ f '' Metric.ball 0 2 := ⟨s z, hsz, hlocal.localInverse_right_inv hz⟩
  apply hinj (Function.invFunOn_mem hzimage) hsz
  rw [Function.invFunOn_eq hzimage, hlocal.localInverse_right_inv hz]

/-- An injective local diffeomorphism on the actual radius-two ball
constructs every field of a surgery ball, including its smooth inverse. -/
noncomputable def surgeryBallOfLocalDiffeomorph
    (f : StandardCapSpace → A.carrier)
    (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2))
    (hinj : Set.InjOn f (Metric.ball 0 2)) : SurgeryBallEmbedding A where
  map := f
  inverse := Function.invFunOn f (Metric.ball 0 2)
  map_smooth := hf.contMDiffOn
  inverse_smooth := ball_local_inverse_smooth f hf hinj
  left_inverse := hinj.leftInvOn_invFunOn
  right_inverse := fun _ hx => Function.invFunOn_eq hx
  open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball
    hf.contMDiffOn (ball_local_inverse_smooth f hf hinj) hinj.leftInvOn_invFunOn

/-- A complete finite description of the nontrivial fibers descends a
filled ball disjoint from all corresponding images. The descended closed
ball is exactly the cover image of the original one, and its center is
the original center's image. This is the ball-descent step of the
spaceform irreducibility argument in Proposition 15.3, pp. 357-358. -/
theorem exists_surgeryBall_descend_finite_fibers
    {Q : GeneralizedSliceCarrier.{u}} (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    {I : Type*} [Finite I] (f : I → A.carrier → A.carrier)
    (hf : ∀ i, Continuous (f i))
    (hfibers : ∀ x y, q x = q y → x = y ∨ ∃ i, y = f i x)
    (B : SurgeryBallEmbedding A)
    (hdisjoint : ∀ i, Disjoint B.closedBall (f i '' B.closedBall)) :
    ∃ D : SurgeryBallEmbedding Q,
      D.closedBall = q '' B.closedBall ∧ D.map 0 = q (B.map 0) := by
  obtain ⟨C, hCB, hcenter, hsep⟩ :=
    exists_surgeryBall_with_disjoint_finite_images B f hf hdisjoint
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞
      (q ∘ C.map) (Metric.ball 0 2) := by
    intro x
    exact (surgeryBall_map_localDiffeomorph A C x.property).comp (𝓡 3) Q.carrier
      (hq (C.map x.val))
  have hinj : Set.InjOn (q ∘ C.map) (Metric.ball 0 2) := by
    intro x hx y hy hxy
    rcases hfibers (C.map x) (C.map y) hxy with heq | ⟨i, hi⟩
    · exact C.left_inverse.injOn hx hy heq
    · exact (Set.disjoint_left.mp (hsep i)
        (Set.mem_image_of_mem C.map hy)
        ⟨C.map x, Set.mem_image_of_mem C.map hx, hi.symm⟩).elim
  refine ⟨surgeryBallOfLocalDiffeomorph (q ∘ C.map) hlocal hinj, ?_, ?_⟩
  · change (q ∘ C.map) '' Metric.closedBall 0 1 = q '' B.closedBall
    rw [Set.image_comp]
    exact congrArg (fun S => q '' S) hCB
  · change q (C.map 0) = q (B.map 0)
    rw [hcenter]

end PoincareMT.M38
