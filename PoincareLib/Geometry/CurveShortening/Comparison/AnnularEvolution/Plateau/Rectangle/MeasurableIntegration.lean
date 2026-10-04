import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Rectangle.GreenIdentity

/-!
# Rectangle integration for measurable derivative columns

The volume-preserving coordinate map works for arbitrary integrable
columns. No continuity of the derivatives is required.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace PoincareMT

open Proofs.M58

/-- Closed and open annular rectangles carry the same restricted volume measure. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Annulus_restrict_closed_eq_interior :
    volume.restrict m64AnnulusDomain = volume.restrict (interior m64AnnulusDomain) := by
  apply Measure.restrict_congr_set
  apply ae_eq_set.mpr
  exact ⟨m64AnnulusDomain_boundary_null, by rw [sdiff_eq_empty.mpr interior_subset]; simp⟩

/-- The actual product coordinate map preserves the restricted annular volume measure. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusPoint_measurePreserving :
    MeasurePreserving (fun q : ℝ × ℝ => annulusPoint q.1 q.2)
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod (volume.restrict (Icc (0 : ℝ) 1)))
      (volume.restrict (interior m64AnnulusDomain)) := by
  have heq : (fun q : ℝ × ℝ => annulusPoint q.1 q.2) = loopPlaneEquivProd.symm := by
    funext q
    ext i
    fin_cases i <;> rfl
  have hpre : loopPlaneEquivProd.symm ⁻¹' m64AnnulusDomain =
      Icc (0 : ℝ) curvePeriod ×ˢ Icc (0 : ℝ) 1 := by
    ext q
    rw [← heq]
    change (0 ≤ q.1 ∧ q.1 ≤ curvePeriod ∧ 0 ≤ q.2 ∧ q.2 ≤ 1) ↔
      (0 ≤ q.1 ∧ q.1 ≤ curvePeriod) ∧ (0 ≤ q.2 ∧ q.2 ≤ 1)
    tauto
  have h := measurePreserving_loopPlaneEquivProd.symm.restrict_preimage_emb
    loopPlaneEquivProd.symm.measurableEmbedding m64AnnulusDomain
  rw [hpre, m64Annulus_restrict_closed_eq_interior] at h
  rw [heq, Measure.prod_restrict]
  exact h

/-- Compute an actual Bochner-integrable annulus integral by the product coordinates. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusInteriorIntegral_eq_iterated_integrable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : LoopPlane → F) (hf : IntegrableOn f (interior m64AnnulusDomain) volume) :
    (∫ p in interior m64AnnulusDomain, f p) =
      ∫ x in Icc (0 : ℝ) curvePeriod, ∫ s in Icc (0 : ℝ) 1, f (annulusPoint x s) := by
  have hi := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hf
  calc
    _ = ∫ q : ℝ × ℝ, f (annulusPoint q.1 q.2)
        ∂((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
          (volume.restrict (Icc (0 : ℝ) 1))) :=
      (m64AnnulusPoint_measurePreserving.integral_comp
        (by
          have heq : (fun q : ℝ × ℝ => annulusPoint q.1 q.2) = loopPlaneEquivProd.symm := by
            funext q
            ext i
            fin_cases i <;> rfl
          rw [heq]
          exact loopPlaneEquivProd.symm.measurableEmbedding) f).symm
    _ = _ := integral_prod _ hi

/-- Swap the two coordinate integrals for genuine Bochner-integrable annular data. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusInteriorIntegral_eq_iterated_swap_integrable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : LoopPlane → F) (hf : IntegrableOn f (interior m64AnnulusDomain) volume) :
    (∫ p in interior m64AnnulusDomain, f p) =
      ∫ s in Icc (0 : ℝ) 1, ∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x s) := by
  rw [m64AnnulusInteriorIntegral_eq_iterated_integrable f hf]
  exact integral_integral_swap (m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hf)

end PoincareMT
