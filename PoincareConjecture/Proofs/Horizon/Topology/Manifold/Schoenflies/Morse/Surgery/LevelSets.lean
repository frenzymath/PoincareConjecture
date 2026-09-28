import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.LevelComponents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem level_eq_and_eventuallyEq_of_disk_splicing
    (f f' : S2 -> E3) (v : E3) (c : Real)
    (e d : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (hdclosed : d '' closedBall 0 1 = (e '' ball 0 1)ᶜ)
    (g : E2 -> E3)
    (hcap : ∀ x ∈ closedBall 0 1, f' (d x) = g x)
    (hoff : ∀ p ∈ e '' closedBall 0 1, f' p = f p)
    (havoid : ∀ x ∈ closedBall 0 1, inner Real v (g x) ≠ c) :
    (fun p => inner Real v (f' p)) ⁻¹' {c} =
      ((fun p => inner Real v (f p)) ⁻¹' {c}) ∩ e '' ball 0 1 ∧
    ∀ p, inner Real v (f' p) = c ->
      (fun q => inner Real v (f' q)) =ᶠ[𝓝 p] (fun q => inner Real v (f q)) := by
  have hretained (p : S2) (hp : inner Real v (f' p) = c) : p ∈ e '' ball 0 1 := by
    by_contra hnot
    have hmem : p ∈ d '' closedBall 0 1 := by rw [hdclosed]; exact hnot
    obtain ⟨x, hx, hxp⟩ := hmem
    apply havoid x hx
    rw [← hcap x hx, hxp, hp]
  have heq : (fun p => inner Real v (f' p)) ⁻¹' {c} =
      ((fun p => inner Real v (f p)) ⁻¹' {c}) ∩ e '' ball 0 1 := by
    ext p
    constructor
    · intro hp
      have he := hretained p hp
      refine ⟨?_, he⟩
      change inner Real v (f p) = c
      rw [← hoff p (image_mono ball_subset_closedBall he)]
      exact hp
    · rintro ⟨hp, he⟩
      change inner Real v (f' p) = c
      rw [hoff p (image_mono ball_subset_closedBall he)]
      exact hp
  refine ⟨heq, ?_⟩
  intro p hp
  filter_upwards [(e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hesource)).mem_nhds (hretained p hp)] with q hq
  rw [hoff q (image_mono ball_subset_closedBall hq)]

theorem regular_level_of_disk_splicing
    (f f' : S2 -> E3) (v : E3) (c : Real)
    (e d : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (hdclosed : d '' closedBall 0 1 = (e '' ball 0 1)ᶜ)
    (g : E2 -> E3)
    (hcap : ∀ x ∈ closedBall 0 1, f' (d x) = g x)
    (hoff : ∀ p ∈ e '' closedBall 0 1, f' p = f p)
    (havoid : ∀ x ∈ closedBall 0 1, inner Real v (g x) ≠ c)
    (hregular : ∀ p, inner Real v (f p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    ∀ p, inner Real v (f' p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f' q)) p ≠ 0 := by
  obtain ⟨hlevel, hlocal⟩ := level_eq_and_eventuallyEq_of_disk_splicing
    f f' v c e d hesource hdclosed g hcap hoff havoid
  intro p hp
  rw [(hlocal p hp).mfderiv_eq]
  exact hregular p (by
    have hmem : p ∈ (fun q => inner Real v (f' q)) ⁻¹' {c} := hp
    rw [hlevel] at hmem
    exact hmem.1)

end Poincare.Manifold.Schoenflies
