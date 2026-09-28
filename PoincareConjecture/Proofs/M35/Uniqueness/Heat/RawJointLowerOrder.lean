import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

theorem rawFirstOrderCoefficient_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawFirstOrderCoefficient (F.connection p.1) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro L
  simp only [rawFirstOrderCoefficient_apply]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  apply (raw_inverseGram_entry_family_contDiffOn F i j).smul
  have hC := rawConnectionCoefficient_family_contDiffOn F
  exact (((hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const)).sub
      (L.contDiff.comp_contDiffOn ((hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const))

theorem rawZeroOrderCoefficient_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawZeroOrderCoefficient (F.connection p.1) p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro z
  simp only [rawZeroOrderCoefficient_apply]
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    apply (raw_inverseGram_entry_family_contDiffOn F i j).smul
    have hC := rawConnectionCoefficient_family_contDiffOn F
    have hdC := rawConnectionDerivative_family_contDiffOn F
    exact ((((hdC.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const).add ((hC.clm_apply contDiffOn_const).clm_apply
        ((hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const))).sub
          ((hC.clm_apply ((hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const)).clm_apply
            contDiffOn_const)
  · exact (rawRicciLinear_family_contDiffOn F).clm_apply contDiffOn_const

theorem rawDivergenceCorrection_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawDivergenceCorrection (F.metric p.1) p.2)
      (J ×ˢ univ) := by
  unfold rawDivergenceCorrection
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact ((rawInverseGramDerivative_family_contDiffOn F i j).clm_apply
    contDiffOn_const).smul contDiffOn_const

theorem rawDivergenceFirstOrder_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawDivergenceFirstOrder (F.connection p.1) p.2)
      (J ×ˢ univ) :=
  (rawFirstOrderCoefficient_family_contDiffOn F).sub (rawDivergenceCorrection_family_contDiffOn F)

theorem rawFirstComponent_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (k j i : Fin n) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => rawFirstComponent (F.connection p.1) k j i p.2) (J ×ˢ univ) := by
  exact (EuclideanSpace.proj k : V →L[ℝ] ℝ).contDiff.comp_contDiffOn
    ((rawDivergenceFirstOrder_family_contDiffOn F).clm_apply
      (contDiffOn_const (c := rawElementaryDerivative i j)))

theorem rawZeroComponent_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (k j : Fin n) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => rawZeroComponent (F.connection p.1) k j p.2) (J ×ˢ univ) := by
  exact (EuclideanSpace.proj k : V →L[ℝ] ℝ).contDiff.comp_contDiffOn
    ((rawZeroOrderCoefficient_family_contDiffOn F).clm_apply (contDiffOn_const (c := e j)))

end PoincareConjecture.M35.Uniqueness.Heat
