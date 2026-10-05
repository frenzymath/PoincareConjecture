import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerBoundaryArc

/-!
# The actual Jordan arc captured by a target neighborhood

Compact embeddedness excludes the rest of the loop from a neighborhood
of the chosen point. This is the arc on which the genuine local inverse
parameter and tangent extension apply. Source: M65 derivation 43,
actual target frame, for Heinz 1970, pp. 99--105, and
MT 19.2, pp. 438--439.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT.M65StrictTrace

/-- A genuine embedded loop has an actual target neighborhood meeting
only the chosen open angular arc. Source: derivation 43,
embedded arc capture for the actual target frame. -/
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

end PoincareMT.M65StrictTrace
