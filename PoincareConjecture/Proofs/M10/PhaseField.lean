import PoincareConjecture.Proofs.M10.KineticLagrangian
import PoincareConjecture.Proofs.M10.MetricInverse









set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M10

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y]


noncomputable def phaseField (B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ) (R : Y × ℝ → ℝ)
    (a : ℝ × Y × (Y →L[ℝ] ℝ)) : ℝ × Y × (Y →L[ℝ] ℝ) :=
  (1, phaseVelocity B a,
    (fderiv ℝ (kineticLagrangian B R) (a.1, a.2.1, phaseVelocity B a)).comp
      ((0 : Y →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.id ℝ Y).prod (0 : Y →L[ℝ] Y))))


theorem phaseField_contDiffAt {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {R : Y × ℝ → ℝ}
    {a : ℝ × Y × (Y →L[ℝ] ℝ)}
    (hB : ContDiffAt ℝ ∞ B (a.2.1, a.1))
    (hR : ContDiffAt ℝ ∞ R (a.2.1, a.1)) (ht : 0 < a.1)
    (hi : (B (a.2.1, a.1)).IsInvertible) :
    ContDiffAt ℝ 1 (phaseField B R) a := by
  have hV : ContDiffAt ℝ 1 (phaseVelocity B) a :=
    (phaseVelocity_contDiffAt hB ht hi).of_le (by simp)
  have hL : ContDiffAt ℝ ∞ (kineticLagrangian B R)
      (a.1, a.2.1, phaseVelocity B a) := kineticLagrangian_contDiffAt hB hR ht
  have hs : ContDiffAt ℝ 1
      (fun b : ℝ × Y × (Y →L[ℝ] ℝ) ↦ (b.1, b.2.1, phaseVelocity B b)) a :=
    contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk hV)
  have hLtwo : ContDiffAt ℝ 2 (kineticLagrangian B R)
      (a.1, a.2.1, phaseVelocity B a) :=
    hL.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact contDiffAt_const.prodMk (hV.prodMk
    (((hLtwo.fderiv_right (m := 1) (by norm_num)).comp a hs).clm_comp contDiffAt_const))

end PoincareConjecture.M10
