import PoincareLib.Analysis.Sobolev.Boundary.Embedding.Subcritical

/-!
# The planar critical Sobolev gain at a flat boundary

A compactly supported H1 function on a half-plane belongs to every finite
Lp space. The support may meet the boundary. Lowering the initial exponent
to 2q/(q+2) makes the existing reflected subcritical estimate apply.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareMT

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Compact support and the reflected subcritical estimate give every finite planar H1
integrability gain, including support meeting the face. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-25-boundary-coordinate-swap.md`. -/
theorem m64HalfSpace_H1_memLp {u : Plane → ℝ}
    (hc : HasCompactSupport u) (hu : MemW1p 2 u (halfSpace 2))
    {q : ℝ} (hq : 1 ≤ q) :
    MemLp u (ENNReal.ofReal q) (volume.restrict (halfSpace 2)) := by
  have hu1 : MemWkp 1 2 u (halfSpace 2) := MemWkp.one_iff_memW1p.mpr hu
  by_cases hq2 : q ≤ 2
  · have hq1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      simpa using ENNReal.ofReal_le_ofReal hq
    have hq2e : ENNReal.ofReal q ≤ 2 := by
      simpa using ENNReal.ofReal_le_ofReal hq2
    exact (EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset 1
      isOpen_halfSpace (isClosed_tsupport u) hc.measure_lt_top.ne hq1e hq2e
      (subset_refl _) hu1).memLp
  · have hq2' : 2 < q := lt_of_not_ge hq2
    let p : ℝ := 2 * q / (q + 2)
    have hden : 0 < q + 2 := by linarith
    have hp1 : 1 ≤ p := by
      dsimp only [p]
      rw [le_div_iff₀ hden]
      linarith
    have hp2 : p < 2 := by
      dsimp only [p]
      rw [div_lt_iff₀ hden]
      linarith
    have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa using ENNReal.ofReal_le_ofReal hp1
    have hp2e : ENNReal.ofReal p ≤ 2 := by
      simpa using ENNReal.ofReal_le_ofReal hp2.le
    have hup : MemWkp 1 (ENNReal.ofReal p) u (halfSpace 2) :=
      EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset 1
        isOpen_halfSpace (isClosed_tsupport u) hc.measure_lt_top.ne hp1e hp2e
        (subset_refl _) hu1
    have hemb := BoundaryEmbedding.memWkp_subcritical 0 hp1 hp2 hc hup
    have hexp : 2 * p / (2 - p) = q := by
      dsimp only [p]
      field_simp
      ring
    have hmem := hemb.memLp
    simpa only [Nat.cast_ofNat, hexp, halfSpace] using! hmem

end PoincareMT
