import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.SobolevGraph

/-!
# Extension of compactly supported weak witnesses

The zero extension retains the displayed weak columns. This identifies
the columns used in the cutoff estimates and in the completed graph.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Extend a compactly supported weak Sobolev map and its actual columns by zero. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. M64 derivation
2026-09-26-boundary-semicircle-assembly.md. -/
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

end PoincareMT
