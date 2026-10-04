import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Rectangle.MeasurableIntegration
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.PeriodicHarmonicMinimum

/-! The literal physical rectangles inside the original annulus.
Coordinate transport preserves the given Euclidean volume exactly.
Source: MT Lemma 19.15, pp. 447-449; M64 truncated curvature derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory

namespace PoincareMT.M64

open Proofs.M58

/-- The original angular fundamental interval between two physical radii. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
def annulusRadialRectangle (lo hi : ℝ) : Set LoopPlane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ lo ≤ p 1 ∧ p 1 ≤ hi}

/-- The physical rectangle has exactly the expected product preimage. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
theorem annulusRadialRectangle_preimage (lo hi : ℝ) :
    loopPlaneEquivProd.symm ⁻¹' annulusRadialRectangle lo hi =
      Icc ((0 : ℝ), lo) (curvePeriod, hi) := by
  ext q
  change (0 ≤ q.1 ∧ q.1 ≤ curvePeriod ∧ lo ≤ q.2 ∧ q.2 ≤ hi) ↔
    (0 ≤ q.1 ∧ lo ≤ q.2) ∧ q.1 ≤ curvePeriod ∧ q.2 ≤ hi
  tauto

/-- Each physical radial rectangle is compact, including its four edges. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
theorem annulusRadialRectangle_isCompact (lo hi : ℝ) :
    IsCompact (annulusRadialRectangle lo hi) := by
  have hmap : Continuous (fun p : ℝ × ℝ => annulusPoint p.1 p.2) := by
    unfold annulusPoint
    fun_prop
  have heq : annulusRadialRectangle lo hi =
      (fun p : ℝ × ℝ => annulusPoint p.1 p.2) '' (Icc 0 curvePeriod ×ˢ Icc lo hi) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z 0, z 1), ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hmap

/-- A radial subinterval of [0,1] gives a literal subset of the original annulus. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
theorem annulusRadialRectangle_subset {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1) :
    annulusRadialRectangle lo hi ⊆ m64AnnulusDomain :=
  fun _ hp => ⟨hp.1, hp.2.1, hlo.trans hp.2.2.1, hp.2.2.2.trans hhi⟩

/-- Strictly interior radial faces lie in the genuine smooth covering strip. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
theorem annulusRadialRectangle_subset_strip {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi < 1) :
    annulusRadialRectangle lo hi ⊆ m64AnnulusOpenStrip :=
  fun _ hp => ⟨hlo.trans_le hp.2.2.1, hp.2.2.2.trans_lt hhi⟩

/-- The actual rectangle coordinates preserve the original volume. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
theorem annulusRadialRectangle_measurePreserving (lo hi : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ => annulusPoint q.1 q.2)
      (volume.restrict (Icc ((0 : ℝ), lo) (curvePeriod, hi)))
      (volume.restrict (annulusRadialRectangle lo hi)) := by
  have heq : (fun q : ℝ × ℝ => annulusPoint q.1 q.2) = loopPlaneEquivProd.symm := by
    funext q
    ext i
    fin_cases i <;> rfl
  rw [heq]
  simpa only [annulusRadialRectangle_preimage] using
    measurePreserving_loopPlaneEquivProd.symm.restrict_preimage_emb
      loopPlaneEquivProd.symm.measurableEmbedding (annulusRadialRectangle lo hi)

/-- Actual integrals on a physical annular rectangle equal the product-coordinate integrals.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivation
`proof-work/tasks/M64/derivations/2026-09-26-truncated-curvature.md`. -/
theorem annulusRadialRectangle_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lo hi : ℝ) (f : LoopPlane → E) :
    (∫ p in annulusRadialRectangle lo hi, f p) =
      ∫ q in Icc ((0 : ℝ), lo) (curvePeriod, hi), f (annulusPoint q.1 q.2) := by
  have heq : (fun q : ℝ × ℝ => annulusPoint q.1 q.2) = loopPlaneEquivProd.symm := by
    funext q
    ext i
    fin_cases i <;> rfl
  exact ((annulusRadialRectangle_measurePreserving lo hi).integral_comp
    (heq.symm ▸ loopPlaneEquivProd.symm.measurableEmbedding) f).symm

end PoincareMT.M64
