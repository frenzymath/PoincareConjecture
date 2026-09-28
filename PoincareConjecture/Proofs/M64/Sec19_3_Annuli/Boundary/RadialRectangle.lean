import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusPeriodicHarmonicMinimum

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory

namespace PoincareConjecture.M64

open Proofs.M58

def annulusRadialRectangle (lo hi : ℝ) : Set LoopPlane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ lo ≤ p 1 ∧ p 1 ≤ hi}

theorem annulusRadialRectangle_preimage (lo hi : ℝ) :
    loopPlaneEquivProd.symm ⁻¹' annulusRadialRectangle lo hi =
      Icc ((0 : ℝ), lo) (curvePeriod, hi) := by
  ext q
  change (0 ≤ q.1 ∧ q.1 ≤ curvePeriod ∧ lo ≤ q.2 ∧ q.2 ≤ hi) ↔
    (0 ≤ q.1 ∧ lo ≤ q.2) ∧ q.1 ≤ curvePeriod ∧ q.2 ≤ hi
  tauto

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

theorem annulusRadialRectangle_subset {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1) :
    annulusRadialRectangle lo hi ⊆ m64AnnulusDomain :=
  fun _ hp => ⟨hp.1, hp.2.1, hlo.trans hp.2.2.1, hp.2.2.2.trans hhi⟩

theorem annulusRadialRectangle_subset_strip {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi < 1) :
    annulusRadialRectangle lo hi ⊆ m64AnnulusOpenStrip :=
  fun _ hp => ⟨hlo.trans_le hp.2.2.1, hp.2.2.2.trans_lt hhi⟩

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

end PoincareConjecture.M64
