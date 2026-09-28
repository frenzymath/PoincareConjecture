import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakSobolevGraph

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem m64WeakSobolev_extend_supported
    {S : Set E} (hS : IsOpen S) {u : E → ℝ}
    (hw : MemW1pWitness 2 u S) (hc : HasCompactSupport u) (hs : tsupport u ⊆ S) :
    ∃ H : MemW1pWitness 2 u univ,
      ∀ x i, H.weakGrad x i = S.indicator (fun y => hw.weakGrad y i) x := by
  let hw' : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u S :=
    { memLp := by simpa using hw.memLp
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := fun i => by simpa using hw.weakGrad_component_memLp i
      isWeakGrad := hw.isWeakGrad }
  have hzero := memW01p_of_memW1p_of_tsupport_subset hS
    (by norm_num : (1 : ℝ) < 2) hw'.memW1p hc hs
  let H0 := zeroExtendMemW1pWitnessP hS (by norm_num : (1 : ℝ) < 2) hzero hw'
  let H : MemW1pWitness 2 (S.indicator u) univ :=
    { memLp := by simpa using H0.memLp
      weakGrad := H0.weakGrad
      weakGrad_component_memLp := fun i => by simpa using H0.weakGrad_component_memLp i
      isWeakGrad := H0.isWeakGrad }
  have hid : S.indicator u = u := by
    ext x
    by_cases hx : x ∈ S
    · exact indicator_of_mem hx u
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
  have hresult : ∃ H : MemW1pWitness 2 (S.indicator u) univ,
      ∀ x i, H.weakGrad x i = S.indicator (fun y => hw.weakGrad y i) x := by
    refine ⟨H, ?_⟩
    intro x i
    rfl
  rw [hid] at hresult
  exact hresult

end PoincareConjecture
