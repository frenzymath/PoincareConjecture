import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryArc











set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture.M65StrictTrace




theorem embedded_loop_arc_capture {M : Type*} [TopologicalSpace M] [T2Space M]
    {gamma : LoopCircle → M} (hgamma : Continuous gamma)
    (hinj : Function.Injective gamma) {J : Set ℝ} (hJ : IsOpen J) {s : ℝ} (hs : s ∈ J) :
    ∃ U : Set M, IsOpen U ∧ gamma (m65LoopAngular s) ∈ U ∧
      ∀ q ∈ U, q ∈ range gamma → ∃ t ∈ J, gamma (m65LoopAngular t) = q := by
  let A := m65LoopAngular '' J
  have hA : IsOpen A := m65LoopAngular_open J hJ
  have hbad : IsClosed (gamma '' Aᶜ) :=
    (hgamma.isClosedEmbedding hinj).isClosedMap _ hA.isClosed_compl
  refine ⟨(gamma '' Aᶜ)ᶜ, hbad.isOpen_compl, ?_, ?_⟩
  · rintro ⟨p, hp, he⟩
    have hp' : p = m65LoopAngular s := hinj he
    exact hp (hp' ▸ mem_image_of_mem m65LoopAngular hs)
  · intro q hq hqr
    obtain ⟨p, rfl⟩ := hqr
    have hp : p ∈ A := by
      by_contra hn
      exact hq ⟨p, hn, rfl⟩
    obtain ⟨t, ht, he⟩ := hp
    exact ⟨t, ht, congrArg gamma he⟩

end PoincareConjecture.M65StrictTrace
