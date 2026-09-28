import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Metric

namespace Set

variable {E : Type*} [NormedAddCommGroup E]

theorem isUnitBallPair_of_onePoint_homeomorph {S D : Set E} (hSD : S ⊆ D)
    (H : OnePoint E ≃ₜ OnePoint E)
    (hmark : ∀ x, H x ∈ ((↑) : E → OnePoint E) '' sphere (0 : E) 1 ↔
      x ∈ ((↑) : E → OnePoint E) '' S)
    (hregion : ∀ x, H x ∈ ((↑) : E → OnePoint E) '' closedBall (0 : E) 1 ↔
      x ∈ ((↑) : E → OnePoint E) '' D) : IsUnitBallPair E D S := by
  let iD : D ≃ₜ (((↑) : E → OnePoint E) '' D) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage D
  let iB : closedBall (0 : E) 1 ≃ₜ (((↑) : E → OnePoint E) '' closedBall (0 : E) 1) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (closedBall (0 : E) 1)
  let G : (((↑) : E → OnePoint E) '' D) ≃ₜ
      (((↑) : E → OnePoint E) '' closedBall (0 : E) 1) :=
    H.subtype (fun x => (hregion x).symm)
  let F : D ≃ₜ closedBall (0 : E) 1 := (iD.trans G).trans iB.symm
  have hF (x : D) : ((F x : E) : OnePoint E) = H ((x : E) : OnePoint E) := by
    have heq := congrArg Subtype.val (iB.apply_symm_apply (G (iD x)))
    change ((F x : E) : OnePoint E) = H ((x : E) : OnePoint E) at heq
    exact heq
  refine ⟨hSD, F, ?_⟩
  intro x
  have h := hmark ((x : E) : OnePoint E)
  rw [← hF x, OnePoint.coe_injective.mem_set_image,
    OnePoint.coe_injective.mem_set_image] at h
  exact h.symm

end Set
