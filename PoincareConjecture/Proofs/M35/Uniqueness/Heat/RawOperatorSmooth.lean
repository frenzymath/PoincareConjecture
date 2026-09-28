import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffOperatorSmooth
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerBounds
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawPrincipalPerturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem contDiffOn_raw_principalMultiplier {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier
      (rawCutoffPrincipalCoefficient (F.metric t) η hη i j)) (Icc a b) := by
  apply contDiffOn_actual_cutoff_operator schwartzMultiplierLinear zero_le_one
    (fun f M hM hf => ?_) hab
    (fun p : ℝ × X => (rawCoordinateGram (F.metric p.1) p.2)⁻¹ i j)
    ((raw_inverseGram_entry_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη _ (fun _ _ _ => rfl)
  change ‖schwartzMultiplier f‖ ≤ 1 * M
  rw [one_mul]
  exact ContinuousLinearMap.opNorm_le_bound _ hM (fun u => norm_schwartzMultiplier_le f u hf)

theorem contDiffOn_raw_principalFormOperator {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set X)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) :
    ContDiffOn ℝ ∞ (fun t => principalFormOperator K
      (rawCutoffPrincipalCoefficient (F.metric t) η hη)) (Icc a b) := by
  unfold principalFormOperator
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact contDiffOn_const.clm_comp
    ((contDiffOn_raw_principalMultiplier F hab hJ η hη i j).clm_comp contDiffOn_const)

theorem contDiffOn_raw_firstValueMultiplier {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set X)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k j i : Fin n) :
    ContDiffOn ℝ ∞ (fun t => dirichletValueMultiplier K
      (rawCutoffFirstComponent (F.connection t) η hη k j i)) (Icc a b) := by
  apply contDiffOn_actual_cutoff_operator (dirichletValueMultiplierLinear K) zero_le_one
    (fun f M hM hf => ?_) hab
    (fun p : ℝ × X => rawFirstComponent (F.connection p.1) k j i p.2)
    ((rawFirstComponent_family_contDiffOn F k j i).mono (prod_mono hJ Subset.rfl))
    η hη _ (fun _ _ _ => rfl)
  change ‖dirichletValueMultiplier K f‖ ≤ 1 * M
  rw [one_mul]
  exact norm_dirichletValueMultiplier_le K f hM hf

theorem contDiffOn_raw_zeroValueMultiplier {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set X)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => dirichletValueMultiplier K
      (rawCutoffZeroComponent (F.connection t) η hη k j)) (Icc a b) := by
  apply contDiffOn_actual_cutoff_operator (dirichletValueMultiplierLinear K) zero_le_one
    (fun f M hM hf => ?_) hab
    (fun p : ℝ × X => rawZeroComponent (F.connection p.1) k j p.2)
    ((rawZeroComponent_family_contDiffOn F k j).mono (prod_mono hJ Subset.rfl))
    η hη _ (fun _ _ _ => rfl)
  change ‖dirichletValueMultiplier K f‖ ≤ 1 * M
  rw [one_mul]
  exact norm_dirichletValueMultiplier_le K f hM hf

theorem contDiffOn_raw_scalarLowerOrder {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => dirichletLowerOrder hK
      (rawCutoffFirstComponent (F.connection t) η hη k j)
      (rawCutoffZeroComponent (F.connection t) η hη k j)) (Icc a b) := by
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro i _
    exact (contDiffOn_raw_firstValueMultiplier F hab hJ K η hη k j i).clm_comp contDiffOn_const
  · exact (contDiffOn_raw_zeroValueMultiplier F hab hJ K η hη k j).clm_comp contDiffOn_const

theorem contDiffOn_rawLowerFormOperator {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) :
    ContDiffOn ℝ ∞ (fun t => rawLowerFormOperator (F.connection t) hK η hη) (Icc a b) := by
  unfold rawLowerFormOperator dirichletVectorLowerOrder finiteHilbertMatrix
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact contDiffOn_const.clm_comp
    ((contDiffOn_raw_scalarLowerOrder F hab hJ hK η hη i j).clm_comp contDiffOn_const)

end PoincareConjecture.M35.Uniqueness.Heat
