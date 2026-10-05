import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.ParametricPathSubstitution
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Coordinates.ClosedChartCoefficients

/-!
# Smooth substitution for actual closed-time fields

Morgan-Tian Lemma 6.18, pp. 113-114. Restricting a field to a compact
time set retains its actual within coefficients. M08's genuine spatial
derivative and M09's bounded pointwise operator give smooth substitution
on the Banach path space, without an ambient extension of time.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

universe u

namespace PoincareMT.M14

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {C : Set ℝ}

/-- Bundle a field on its actual time subtype, using only its continuous
values on that time set, the closed-time restriction for Lemma 6.18,
pp. 113-114. -/
def closedTimeField (f : ℝ × E → F) (hf : ContinuousOn f (C ×ˢ univ)) : C(C × E, F) :=
  ⟨fun z => f (z.1.val, z.2), hf.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun z => ⟨z.1.property, mem_univ _⟩)⟩

/-- Substitute a continuous state path into the actual closed-time field,
the path-space operator used for Lemma 6.18, pp. 113-114. -/
def closedTimePostcomp [CompactSpace C] (f : ℝ × E → F)
    (hf : ContinuousOn f (C ×ˢ univ)) : C(C, E) → C(C, F) :=
  parametricPostcomp (closedTimeField f hf)

/-- Restricting the time set preserves the genuine state derivative at
each retained point. This is the coefficient compatibility required
for closed-time local dependence in Lemma 6.18, pp. 113-114. -/
theorem spatialWithinFDeriv_subset_time {D : Set ℝ} {U : Set E} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) (hDC : D ⊆ C)
    {t : ℝ} {x : E} (ht : t ∈ D) (hx : x ∈ U) :
    M08.spatialWithinFDeriv D U f (t, x) = M08.spatialWithinFDeriv C U f (t, x) :=
  (M08.hasFDerivAt_spatialWithin hU f (hf.mono (prod_mono hDC Subset.rfl)) ht hx).unique
    (M08.hasFDerivAt_spatialWithin hU f hf (hDC ht) hx)

/-- The actual spatial within differential gives the path-space
derivative while keeping the compact time parameter fixed,
Lemma 6.18, pp. 113-114. -/
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

/-- Substitution by a smooth actual closed-time field has every finite
derivative order in the path variable. This is the induction underlying
smooth initial-state dependence in Lemma 6.18, pp. 113-114. -/
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

/-- A smooth actual closed-time field induces smooth substitution on
continuous state paths, with no regularity assertion about its off-time
representative, Lemma 6.18, pp. 113-114. -/
theorem closedTimePostcomp_contDiff [CompactSpace C] [FiniteDimensional ℝ E]
    (hC : UniqueDiffOn ℝ C) (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ univ)) :
    ContDiff ℝ ∞ (closedTimePostcomp f hf.continuousOn) :=
  contDiff_infty.mpr fun k => closedTimePostcomp_contDiff_nat hC k f hf

end PoincareMT.M14
