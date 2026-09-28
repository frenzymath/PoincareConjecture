import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleGreenIdentity

set_option autoImplicit false

open Set MeasureTheory

namespace PoincareConjecture

open Proofs.M58

theorem m64Annulus_restrict_closed_eq_interior :
    volume.restrict m64AnnulusDomain = volume.restrict (interior m64AnnulusDomain) := by
  apply Measure.restrict_congr_set
  apply ae_eq_set.mpr
  exact ⟨m64AnnulusDomain_boundary_null, by rw [sdiff_eq_empty.mpr interior_subset]; simp⟩

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

theorem m64AnnulusInteriorIntegral_eq_iterated_swap_integrable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : LoopPlane → F) (hf : IntegrableOn f (interior m64AnnulusDomain) volume) :
    (∫ p in interior m64AnnulusDomain, f p) =
      ∫ s in Icc (0 : ℝ) 1, ∫ x in Icc (0 : ℝ) curvePeriod, f (annulusPoint x s) := by
  rw [m64AnnulusInteriorIntegral_eq_iterated_integrable f hf]
  exact integral_integral_swap (m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hf)

end PoincareConjecture
