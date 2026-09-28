import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSecondDerivativeLp

set_option autoImplicit false

open AddCircle Filter MeasureTheory PoincareConjecture.SpectralHeatNative
open scoped Topology ContDiff

universe u v

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type u} [Fintype ι]
  {Z : Type v} [TopologicalSpace Z] [CompactSpace Z]

local notation "S" => State ((ℤ × Fin 2) × ι)
local notation "W" => EuclideanSpace ℝ ι

theorem exists_spectral_approximation_jets
    (Vn : ℕ → C(Z, S)) (V : C(Z, S))
    (hV : Tendsto Vn atTop (𝓝 V))
    (hphase : ∀ j z, DifferentiableAt ℝ
      (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (Vn j z)) 0) :
    let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
    let D0 := (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 0 (by omega))
    let D1 := (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 1 (by omega))
    let D2 := vectorPeriodicSecondDerivativeLp (L := L) (ι := ι)
    (∀ z (x : ℝ), HasDerivAt (fun y : ℝ => D0 (V z) (y : AddCircle L))
      (D1 (V z) (x : AddCircle L)) x) ∧
    ∃ r : ℕ → Z → C(AddCircle L, W),
      (∀ j z,
        ContDiff ℝ 2 (fun x : ℝ => D0 (Vn j z) (x : AddCircle L)) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => D0 (Vn j z) (y : AddCircle L))
          (D1 (Vn j z) (x : AddCircle L)) x) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => D1 (Vn j z) (y : AddCircle L))
          (r j z (x : AddCircle L)) x) ∧
        (∀ x : ℝ, iteratedDeriv 2
          (fun y : ℝ => D0 (Vn j z) (y : AddCircle L)) x =
            r j z (x : AddCircle L)) ∧
        D2 (Vn j z) = ContinuousMap.toLp 2 haarAddCircle ℝ (r j z)) ∧
      ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ z,
        ‖D0 (Vn j z) - D0 (V z)‖ < eps ∧
        ‖D1 (Vn j z) - D1 (V z)‖ < eps ∧
        ‖ContinuousMap.toLp 2 haarAddCircle ℝ (r j z) - D2 (V z)‖ < eps := by
  classical
  dsimp only
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let D0 : S →L[ℝ] C(AddCircle L, W) :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
    (vectorPeriodicJet (L := L) 1 0 (by omega))
  let D1 : S →L[ℝ] C(AddCircle L, W) :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
    (vectorPeriodicJet (L := L) 1 1 (by omega))
  let D2 := vectorPeriodicSecondDerivativeLp (L := L) (ι := ι)
  have hfirst (u : S) (x : ℝ) :
      HasDerivAt (fun y : ℝ => D0 u (y : AddCircle L)) (D1 u (x : AddCircle L)) x :=
    E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (by omega : 0 < 1) u x)
  choose r hr using fun j z => vectorPeriodicSecondDerivativeLp_spec (Vn j z) (hphase j z)
  have hspec (j : ℕ) (z : Z) :
      ContDiff ℝ 2 (fun x : ℝ => D0 (Vn j z) (x : AddCircle L)) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => D1 (Vn j z) (y : AddCircle L))
        (r j z (x : AddCircle L)) x) ∧
      (∀ x : ℝ, iteratedDeriv 2 (fun y : ℝ => D0 (Vn j z) (y : AddCircle L)) x =
        r j z (x : AddCircle L)) ∧
      D2 (Vn j z) = ContinuousMap.toLp 2 haarAddCircle ℝ (r j z) := hr j z
  refine ⟨fun z => hfirst (V z), r, ?_, ?_⟩
  · intro j z
    exact ⟨(hspec j z).1, hfirst (Vn j z), (hspec j z).2⟩
  · have h0 := (D0.compLeftContinuous ℝ Z).continuous.tendsto V |>.comp hV
    have h1 := (D1.compLeftContinuous ℝ Z).continuous.tendsto V |>.comp hV
    have h2 := (D2.compLeftContinuous ℝ Z).continuous.tendsto V |>.comp hV
    intro eps heps
    obtain ⟨N0, hN0⟩ :=
      (Metric.tendsto_atTop (α := C(Z, C(AddCircle L, W)))).mp h0 eps heps
    obtain ⟨N1, hN1⟩ :=
      (Metric.tendsto_atTop (α := C(Z, C(AddCircle L, W)))).mp h1 eps heps
    obtain ⟨N2, hN2⟩ :=
      (Metric.tendsto_atTop (α := C(Z, Lp W 2 (@haarAddCircle L _)))).mp h2 eps heps
    refine ⟨max N0 (max N1 N2), ?_⟩
    intro j hj z
    have hj0 : N0 ≤ j := (le_max_left _ _).trans hj
    have hj1 : N1 ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
    have hj2 : N2 ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
    have hn0 : ‖D0.compLeftContinuous ℝ Z (Vn j) - D0.compLeftContinuous ℝ Z V‖ < eps := by
      rw [← dist_eq_norm (D0.compLeftContinuous ℝ Z (Vn j)) (D0.compLeftContinuous ℝ Z V)]
      exact hN0 j hj0
    have hn1 : ‖D1.compLeftContinuous ℝ Z (Vn j) - D1.compLeftContinuous ℝ Z V‖ < eps := by
      rw [← dist_eq_norm (D1.compLeftContinuous ℝ Z (Vn j)) (D1.compLeftContinuous ℝ Z V)]
      exact hN1 j hj1
    have h0z := ((D0.compLeftContinuous ℝ Z (Vn j) -
      D0.compLeftContinuous ℝ Z V).norm_coe_le_norm z).trans_lt
        hn0
    have h1z := ((D1.compLeftContinuous ℝ Z (Vn j) -
      D1.compLeftContinuous ℝ Z V).norm_coe_le_norm z).trans_lt
        hn1
    have h2z := ((D2.compLeftContinuous ℝ Z (Vn j) -
      D2.compLeftContinuous ℝ Z V).norm_coe_le_norm z).trans_lt
        (by simpa +instances only [Function.comp_apply, dist_eq_norm] using! hN2 j hj2)
    refine ⟨h0z, h1z, ?_⟩
    change ‖D2 (Vn j z) - D2 (V z)‖ < eps at h2z
    rwa [(hspec j z).2.2.2] at h2z

end PoincareConjecture.M63
