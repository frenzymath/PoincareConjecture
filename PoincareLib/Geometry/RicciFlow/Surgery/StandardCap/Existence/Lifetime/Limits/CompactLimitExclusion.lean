import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Limits.CompactImmersion
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.GeneralizedCylinderDifferential

/-!
# A generalized Euclidean blow-up has noncompact limit carrier

If the whole carrier were compact, it would lie in one actual exhaustion
stage. That stage's spatial map at time zero would immerse the whole
carrier into a source slice diffeomorphic to R3.
Source: Morgan-Tian Theorem 12.28, pp. 323-324; M34 compact-limit exclusion
derivation. No time-interior premise or metric convergence rate is used.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M34

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

/-- The actual limit carrier is noncompact whenever all included source
slices are diffeomorphic to R3 (Theorem 12.28). -/
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

end PoincareMT.M34
