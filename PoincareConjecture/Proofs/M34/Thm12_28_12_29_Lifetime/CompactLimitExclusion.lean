import PoincareConjecture.Proofs.M34.Mathlib.CompactImmersion
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderDifferential











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)



theorem generalizedBlowupConvergence_not_compact
    (hsource : ∀ k t, t ∈ (S.flow k).interval →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3)
        ((S.flow k).slice t).carrier (EuclideanSpace ℝ (Fin 3)) ∞)) :
    ¬ IsCompact (univ : Set C.limit.sliceCarrier.carrier) := by
  intro hcompact
  obtain ⟨k, hk⟩ := hcompact.elim_directed_cover C.exhaustion.space
    C.exhaustion.space_open
    (fun x _ => C.exhaustion.space_covers.symm ▸ mem_univ x)
    C.exhaustion.space_increasing.directed_le
  have hzero : 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  let e := C.embedding k
  have ht : (S.base (C.subsequence k)).1 + 0 / S.scale (C.subsequence k) ∈
      (S.flow (C.subsequence k)).interval :=
    ((S.flow (C.subsequence k)).slice_nonempty_iff _).mp
      ⟨e.forward 0 hzero C.limit.base⟩
  obtain ⟨psi⟩ := hsource (C.subsequence k) _ ht
  let f := psi ∘ e.forward 0 hzero
  have he (x : C.limit.sliceCarrier.carrier) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (e.forward 0 hzero) x :=
    (e.forward_smooth 0 hzero x (hk (mem_univ x))).contMDiffAt
      ((C.exhaustion.space_open k).mem_nhds (hk (mem_univ x)))
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    fun x => (psi.contMDiff _).comp x (he x)
  have hinj (x : C.limit.sliceCarrier.carrier) :
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x) := by
    change Function.Injective (mfderiv (𝓡 3) (𝓡 3) (psi ∘ e.forward 0 hzero) x)
    rw [mfderiv_comp x (psi.mdifferentiable (by simp) _)
      ((he x).mdifferentiableAt (by simp))]
    exact (psi.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (e.forward_mfderiv_injective (C.exhaustion.space_open k) hzero (hk (mem_univ x)))
  exact not_isCompact_univ_of_euclidean_immersion
    (M := C.limit.sliceCarrier.carrier) C.limit.base f hf hinj hcompact

end PoincareConjecture.M34
