import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralTracePrimitive
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicLaplacian
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs









set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]




theorem vectorPeriodicJet_shiftedBase (k j : ℕ) (hj : j ≤ k)
    (u : State ((ℤ × Fin 2) × ι)) :
    vectorPeriodicJet (L := L) k j hj
        (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) u) =
      vectorPeriodicJet (L := L) (k + 1) j (hj.trans (Nat.le_add_right k 1)) u := by
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  have hJ : shiftedBaseMultiplier lambda u = scaleDecode lambda 1 u := by
    apply lp.ext
    funext i
    simp only [shiftedBaseMultiplier, multiplier_apply, scaleDecode_apply,
      scaleWeight, pow_one, one_div]
  change vectorPeriodicJet (L := L) k j hj (shiftedBaseMultiplier lambda u) = _
  rw [hJ, vectorPeriodicJet_scaleDecode]




theorem vectorPeriodicJet_high_second_derivative
    (H V : State ((ℤ × Fin 2) × ι))
    (htrace : shiftedBaseMultiplier
      (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) H = V) (x : ℝ) :
    HasDerivAt (fun y : ℝ => vectorPeriodicJet (L := L) 1 1 (by omega) V (y : AddCircle L))
        (vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L)) x ∧
      iteratedDeriv 2 (fun y : ℝ =>
        vectorPeriodicJet (L := L) 1 0 (by omega) V (y : AddCircle L)) x =
          vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L) := by
  have hfirst : deriv (fun y : ℝ =>
      vectorPeriodicJet (L := L) 1 0 (by omega) V (y : AddCircle L)) =
      fun y : ℝ => vectorPeriodicJet (L := L) 1 1 (by omega) V (y : AddCircle L) := by
    funext y
    exact (hasDerivAt_vectorPeriodicJet (L := L) (k := 1) (j := 0) (by omega) V y).deriv
  have hderiv : HasDerivAt
      (fun y : ℝ => vectorPeriodicJet (L := L) 1 1 (by omega) V (y : AddCircle L))
      (vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L)) x := by
    rw [← htrace, vectorPeriodicJet_shiftedBase]
    exact hasDerivAt_vectorPeriodicJet (L := L) (k := 2) (j := 1) (by omega) H x
  refine ⟨hderiv, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst]
  exact hderiv.deriv





theorem initialResponseTrace_decoded_derivative
    (w : State ((ℤ × Fin 2) × ι)) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace ((ℤ × Fin 2) × ι) T) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    ∀ᵐ t ∂timeMeasure T, ∀ _ht : t ∈ Icc (0 : ℝ) T,
      vectorPeriodicJet (L := L) 0 0 (by omega)
          (-initialHeatGenerator lambda w t + derivativeState lambda F t) =
        vectorPeriodicJet (L := L) 2 2 (by omega)
            (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t) +
          vectorPeriodicJet (L := L) 0 0 (by omega) (F t) := by
  dsimp only
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  filter_upwards [initialResponseTrace_generator lambda w hT F,
    (initialResponseTrace_spec lambda w hT F).2.2.2] with t hgen htrace
  intro ht
  let H := initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t
  let V := initialResponseTrace lambda w hT F ⟨t, ht⟩
  let J := shiftedBaseMultiplier lambda
  have hJV : J V = scaleDecode lambda 2 H := by
    change shiftedBaseMultiplier lambda
        (initialResponseTrace lambda w hT F ⟨t, ht⟩) = _
    rw [← htrace ht]
    apply lp.ext
    funext i
    simp only [shiftedBaseMultiplier, multiplier_apply, scaleDecode_apply,
      scaleWeight, one_div, pow_two, mul_inv]
    ring
  have hD : -initialHeatGenerator lambda w t + derivativeState lambda F t =
      F t - (H - J V) := by
    have h1 := (hgen ht).1
    have h2 := (hgen ht).2
    change H - J V = initialHeatGenerator lambda w t + generatorState lambda F t at h1
    rw [h1]
    exact eq_sub_iff_add_eq.mpr h2
  rw [hD, map_sub]
  have hlap := vectorPeriodicJet_laplacian (L := L) H
  rw [← hJV] at hlap
  rw [hlap]
  abel




theorem initialResponseTrace_decoded_integral
    (w : State ((ℤ × Fin 2) × ι)) {T : ℝ} (hT : 0 ≤ T)
    (F : ForcingSpace ((ℤ × Fin 2) × ι) T) (t : Icc (0 : ℝ) T) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    vectorPeriodicJet (L := L) 1 0 (by omega) (initialResponseTrace lambda w hT F t) =
      vectorPeriodicJet (L := L) 1 0 (by omega) w + ∫ s in (0 : ℝ)..(t : ℝ),
        vectorPeriodicJet (L := L) 0 0 (by omega)
          (-initialHeatGenerator lambda w s + derivativeState lambda F s) := by
  dsimp only
  have h := initialResponseTrace_integral_comp
    (E := C(AddCircle L, ι → ℝ))
    (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) w hT F
    (vectorPeriodicJet (L := L) (ι := ι) 0 0 (by omega)) t
  rw [vectorPeriodicJet_shiftedBase, vectorPeriodicJet_shiftedBase] at h
  exact h

end PoincareConjecture.M63
