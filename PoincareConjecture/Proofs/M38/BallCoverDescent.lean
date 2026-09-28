import PoincareConjecture.Proofs.M38.SurgeryBallNeighborhood











set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}



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

end PoincareConjecture.M38
