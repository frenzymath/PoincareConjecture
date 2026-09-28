import PoincareConjecture.Proofs.M14.Mathlib.ParametricPathSubstitution
import PoincareConjecture.Proofs.M08.ClosedChartCoefficients










set_option autoImplicit false

open Set
open scoped ContDiff

universe u

namespace PoincareConjecture.M14

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {C : Set ℝ}




def closedTimeField (f : ℝ × E → F) (hf : ContinuousOn f (C ×ˢ univ)) : C(C × E, F) :=
  ⟨fun z => f (z.1.val, z.2), hf.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun z => ⟨z.1.property, mem_univ _⟩)⟩



def closedTimePostcomp [CompactSpace C] (f : ℝ × E → F)
    (hf : ContinuousOn f (C ×ˢ univ)) : C(C, E) → C(C, F) :=
  parametricPostcomp (closedTimeField f hf)




theorem spatialWithinFDeriv_subset_time {D : Set ℝ} {U : Set E} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) (hDC : D ⊆ C)
    {t : ℝ} {x : E} (ht : t ∈ D) (hx : x ∈ U) :
    M08.spatialWithinFDeriv D U f (t, x) = M08.spatialWithinFDeriv C U f (t, x) :=
  (M08.hasFDerivAt_spatialWithin hU f (hf.mono (prod_mono hDC Subset.rfl)) ht hx).unique
    (M08.hasFDerivAt_spatialWithin hU f hf (hDC ht) hx)




theorem hasFDerivAt_closedTimePostcomp [CompactSpace C] [FiniteDimensional ℝ E]
    (hC : UniqueDiffOn ℝ C) (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ univ))
    (φ : C(C, E)) :
    HasFDerivAt (closedTimePostcomp f hf.continuousOn)
      (Proofs.M09.pointwiseLinear
        (closedTimePostcomp (M08.spatialWithinFDeriv C univ f)
          (M08.spatialWithinFDeriv_contDiffOn hC isOpen_univ f hf).continuousOn φ)) φ := by
  apply hasFDerivAt_parametricPostcomp
  intro t x
  exact M08.hasFDerivAt_spatialWithin isOpen_univ f hf t.property (mem_univ x)




theorem closedTimePostcomp_contDiff_nat [CompactSpace C] [FiniteDimensional ℝ E]
    (hC : UniqueDiffOn ℝ C) (k : ℕ) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ ∞ f (C ×ˢ univ)) :
    ContDiff ℝ k (closedTimePostcomp f hf.continuousOn) := by
  induction k generalizing F with
  | zero =>
    exact contDiff_zero.mpr (continuous_parametricPostcomp (closedTimeField f hf.continuousOn))
  | succ k ih =>
    have hD := M08.spatialWithinFDeriv_contDiffOn hC isOpen_univ f hf
    simp only [Nat.cast_add, Nat.cast_one]
    refine contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fun φ => Proofs.M09.pointwiseLinear
        (closedTimePostcomp (M08.spatialWithinFDeriv C univ f) hD.continuousOn φ), ?_,
        fun φ => hasFDerivAt_closedTimePostcomp hC f hf φ⟩
    exact (Proofs.M09.pointwiseOperator (K := C) (E := E) (F := F)).contDiff.comp
      (ih (M08.spatialWithinFDeriv C univ f) hD)




theorem closedTimePostcomp_contDiff [CompactSpace C] [FiniteDimensional ℝ E]
    (hC : UniqueDiffOn ℝ C) (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ univ)) :
    ContDiff ℝ ∞ (closedTimePostcomp f hf.continuousOn) :=
  contDiff_infty.mpr fun k => closedTimePostcomp_contDiff_nat hC k f hf

end PoincareConjecture.M14
