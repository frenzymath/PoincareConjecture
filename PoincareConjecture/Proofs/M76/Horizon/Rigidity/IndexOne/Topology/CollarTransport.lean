import PoincareConjecture.Proofs.M76.Brown.SpindleHeight
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
open Set BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_local_collar_of_parametrized_collar
    {C S T B : Type*} [TopologicalSpace C] [TopologicalSpace S]
    [TopologicalSpace T] [TopologicalSpace B]
    (H : T ≃ₜ S) (gamma : C ≃ₜ B) (f : C → S) (i : B → T)
    (hcomm : ∀ z, H (i (gamma z)) = f z)
    {U : Set S} (hU : IsOpen U)
    (d : (C × Ico (0 : ℝ) 1) ≃ₜ U)
    (hbase : ∀ z, (d (collarBase z) : S) = f z) :
    ∀ x : B, ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) T,
      collarBase x ∈ c.source ∧
        ∀ a, collarBase a ∈ c.source → c (collarBase a) = i a := by
  intro x
  let O : TopologicalSpace.Opens S := ⟨U, hU⟩
  let j := O.openPartialHomeomorphSubtypeCoe ⟨d (collarBase (gamma.symm x))⟩
  let D := (gamma.symm.prodCongr (Homeomorph.refl (Ico (0 : ℝ) 1))).trans d
  let c := (D.transOpenPartialHomeomorph j).transHomeomorph H.symm
  refine ⟨c, ?_, ?_⟩
  · change D (collarBase x) ∈ j.source
    trivial
  · intro a _
    change H.symm (d (collarBase (gamma.symm a))) = i a
    rw [hbase, ← hcomm, gamma.apply_symm_apply, H.symm_apply_apply]

end PoincareConjecture.M76.HamiltonIntervalTorus
