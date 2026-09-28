import PoincareConjecture.Proofs.M03.Existence.HilbertFormBasisNative
import PoincareConjecture.Proofs.M03.Existence.HilbertParabolicNative
import PoincareConjecture.Proofs.M03.Existence.SpectralScaleNative

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.HilbertResolventNative

open SpectralHeatNative (State)

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def scaleValue (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) :
    State (EigenIndex J) →L[ℝ] H :=
  (eigenbasis J hc hd).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (SpectralHeatNative.scaleDecode (generatorParameters J hc hd hnorm) k)

@[simp] theorem scaleValue_apply (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) (z : State (EigenIndex J)) :
    scaleValue J hc hd hnorm k z = (eigenbasis J hc hd).repr.symm
      (SpectralHeatNative.scaleDecode (generatorParameters J hc hd hnorm) k z) := rfl

theorem repr_scaleValue (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) (z : State (EigenIndex J)) :
    (eigenbasis J hc hd).repr (scaleValue J hc hd hnorm k z) =
      SpectralHeatNative.scaleDecode (generatorParameters J hc hd hnorm) k z := by
  rw [scaleValue_apply, LinearIsometryEquiv.apply_symm_apply]

theorem norm_scaleValue_le (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) (z : State (EigenIndex J)) :
    ‖scaleValue J hc hd hnorm k z‖ ≤ ‖z‖ := by
  rw [scaleValue_apply, LinearIsometryEquiv.norm_map]
  exact SpectralHeatNative.norm_scaleDecode_le _ _ _

theorem scaleValue_injective (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) :
    Function.Injective (scaleValue J hc hd hnorm k) := by
  intro z w heq
  apply SpectralHeatNative.scaleDecode_injective (generatorParameters J hc hd hnorm) k
  simpa only [repr_scaleValue] using congrArg (eigenbasis J hc hd).repr heq

theorem scaleValue_denseRange (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) :
    DenseRange (scaleValue J hc hd hnorm k) :=
  (eigenbasis J hc hd).repr.symm.surjective.denseRange.comp
    (SpectralHeatNative.scaleDecode_denseRange _ _) (eigenbasis J hc hd).repr.symm.continuous

def InHilbertScale (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) (u : H) : Prop :=
  SpectralHeatNative.InScale (generatorParameters J hc hd hnorm) k
    ((eigenbasis J hc hd).repr u)

theorem inHilbertScale_iff_mem_range (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (k : ℕ) (u : H) :
    InHilbertScale J hc hd hnorm k u ↔ u ∈ Set.range (scaleValue J hc hd hnorm k) := by
  rw [InHilbertScale, SpectralHeatNative.inScale_iff_mem_range]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply (eigenbasis J hc hd).repr.injective
    rw [repr_scaleValue, hz]
  · rintro ⟨z, rfl⟩
    exact ⟨z, (repr_scaleValue J hc hd hnorm k z).symm⟩

theorem scaleValue_one (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J) (hnorm : ‖J‖ ≤ 1)
    (z : State (EigenIndex J)) :
    scaleValue J hc hd hnorm 1 z = J ((formEigenbasis J hc hd hinj).repr.symm z) := by
  apply (eigenbasis J hc hd).repr.injective
  apply lp.ext
  funext i
  rw [repr_scaleValue, SpectralHeatNative.scaleDecode_apply, repr_inclusion_decode]
  change (Real.sqrt (1 + (generatorParameters J hc hd hnorm i : ℝ)) ^ 1)⁻¹ * z i =
    Real.sqrt i.1.val * z i
  rw [pow_one]
  have hq : Real.sqrt (1 + (generatorParameters J hc hd hnorm i : ℝ)) ≠ 0 := by positivity
  have heq : Real.sqrt i.1.val =
      (Real.sqrt (1 + (generatorParameters J hc hd hnorm i : ℝ)))⁻¹ := by
    rw [inv_eq_one_div]
    exact (eq_div_iff hq).mpr (sqrt_eigenparameter_mul_shifted J hc hd hnorm i)
  rw [heq]

theorem inHilbertScale_one_iff (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hinj : Function.Injective J) (hnorm : ‖J‖ ≤ 1) (u : H) :
    InHilbertScale J hc hd hnorm 1 u ↔ u ∈ Set.range J := by
  rw [inHilbertScale_iff_mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(formEigenbasis J hc hd hinj).repr.symm z,
      (scaleValue_one J hc hd hinj hnorm z).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨(formEigenbasis J hc hd hinj).repr v, ?_⟩
    rw [scaleValue_one J hc hd hinj hnorm, LinearIsometryEquiv.symm_apply_apply]

theorem scaleValue_two (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (z : State (EigenIndex J)) :
    scaleValue J hc hd hnorm 2 z = operator J ((eigenbasis J hc hd).repr.symm z) := by
  apply (eigenbasis J hc hd).repr.injective
  apply lp.ext
  funext i
  rw [repr_scaleValue, SpectralHeatNative.scaleDecode_apply,
    SpectralHeatNative.scaleWeight_two, repr_operator, LinearIsometryEquiv.apply_symm_apply]
  have heq : 1 + (generatorParameters J hc hd hnorm i : ℝ) = i.1.val⁻¹ := by
    rw [generatorParameters_coe]
    ring
  rw [heq, inv_inv]

theorem inHilbertScale_two_iff (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1) (u : H) :
    InHilbertScale J hc hd hnorm 2 u ↔ ∃ a : H, InGeneratorGraph J u a := by
  rw [inHilbertScale_iff_mem_range]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(eigenbasis J hc hd).repr.symm z - u, ?_⟩
    change operator J (u + ((eigenbasis J hc hd).repr.symm z - u)) = u
    rw [show u + ((eigenbasis J hc hd).repr.symm z - u) =
      (eigenbasis J hc hd).repr.symm z by abel, ← scaleValue_two J hc hd hnorm, hz]
  · rintro ⟨a, ha⟩
    refine ⟨(eigenbasis J hc hd).repr (u + a), ?_⟩
    rw [scaleValue_two J hc hd hnorm, LinearIsometryEquiv.symm_apply_apply]
    exact ha

theorem scaleValue_shiftedHigh [SeparableSpace H] (J : V →L[ℝ] H)
    (hc : IsCompactOperator J) (hd : DenseRange J) (hnorm : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (F : SpectralHeatNative.ForcingSpace (EigenIndex J) T) :
    letI : Countable (EigenIndex J) := eigenIndex_countable J hc
    ∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
      scaleValue J hc hd hnorm 2
        (SpectralHeatNative.shiftedHighOperator hT (generatorParameters J hc hd hnorm) F t) =
      (eigenbasis J hc hd).repr.symm
        (SpectralHeatNative.responseState (generatorParameters J hc hd hnorm) F t) := by
  haveI : Countable (EigenIndex J) := eigenIndex_countable J hc
  filter_upwards [SpectralHeatNative.scaleDecode_shiftedHigh hT
    (generatorParameters J hc hd hnorm) F] with t ht
  rw [scaleValue_apply, ht]

end PoincareConjecture.HilbertResolventNative
