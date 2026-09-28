import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoefficientTimeJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeOperatorJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.VectorDivergence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

local instance rawGeneratorTimeJetsOpNorm (K : Set X) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin n => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin n => dirichletForm K)) := ContinuousLinearMap.toNormedAddCommGroup

local instance rawGeneratorTimeJetsOpSpace (K : Set X) :
    NormedSpace ℝ (PiLp 2 (fun _ : Fin n => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin n => dirichletForm K)) := ContinuousLinearMap.toNormedSpace

def rawVectorGeneratorTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (t : ℝ) :
    PiLp 2 (fun _ : Fin n => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin n => dirichletForm K) :=
  (finiteHilbertMap (dirichletInclusion K)).adjoint.comp
    (dirichletVectorLowerOrder hK (rawFirstTimeJet F hab hJ η hη k t)
      (rawZeroTimeJet F hab hJ η hη k t)) -
    finiteHilbertMap (principalFormOperator K (rawPrincipalTimeJet F hab hJ η hη k t))

theorem hasDerivWithinAt_rawVectorGeneratorTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (rawVectorGeneratorTimeJet F hab hJ hK η hη k)
      (rawVectorGeneratorTimeJet F hab hJ hK η hη (k + 1) t) (Icc a b) t := by
  have hP := (finiteHilbertMapOperator (E := dirichletForm K) (F := dirichletForm K)
    (m := n)).hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_rawPrincipalFormTimeJet F hab hJ K η hη k ht)
  have hL := (hasDerivWithinAt_const t (Icc a b)
    (finiteHilbertMap (dirichletInclusion K)).adjoint).clm_comp
      (hasDerivWithinAt_rawLowerFormTimeJet F hab hJ hK η hη k ht)
  simpa only [rawVectorGeneratorTimeJet, ContinuousLinearMap.zero_comp, zero_add,
    finiteHilbertMapOperator_apply, Function.comp_def, Pi.sub_apply] using! hL.fun_sub hP

theorem rawVectorGeneratorTimeJet_pairing {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (t : ℝ)
    (z u : PiLp 2 (fun _ : Fin n => dirichletForm K)) :
    inner ℝ z (rawVectorGeneratorTimeJet F hab hJ hK η hη k t u) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (dirichletVectorLowerOrder hK (rawFirstTimeJet F hab hJ η hη k t)
          (rawZeroTimeJet F hab hJ η hη k t) u) -
        principalVectorEnergy K (rawPrincipalTimeJet F hab hJ η hη k t) z u := by
  simp only [rawVectorGeneratorTimeJet, sub_apply, inner_sub_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    principalVectorEnergy_pairing]

theorem raw_compact_heat_timeJet_equation {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η)
    (w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hw : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ w t)
    (heq : ∀ t ∈ Ioo a b, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (deriv w t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection t) hK η hη (w t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη) z (w t))
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) :
    (finiteHilbertMap (dirichletInclusion K)).adjoint
      (finiteHilbertMap (dirichletInclusion K) (iteratedDeriv (k + 1) w t)) =
        timeOperatorJet (rawVectorGeneratorTimeJet F hab hJ hK η hη) (fun j => iteratedDeriv j w)
          k t := by
  let I := finiteHilbertMap (m := n) (dirichletInclusion K)
  apply linearHeat_timeJet_equation (I.adjoint.comp I)
    (rawVectorGeneratorTimeJet F hab hJ hK η hη) (fun j => iteratedDeriv j w) isOpen_Ioo
  · intro j s hs
    exact (hasDerivWithinAt_rawVectorGeneratorTimeJet F hab hJ hK η hη j
      (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  · intro j s hs
    exact hasDerivAt_iteratedDeriv_infty (hw s hs) j
  · intro s hs
    apply ext_inner_left ℝ
    intro z
    have hleft : inner ℝ z ((I.adjoint.comp I) (iteratedDeriv 1 w s)) =
        inner ℝ (I z) (I (deriv w s)) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        iteratedDeriv_one]
    exact hleft.trans ((heq s hs z).trans (by
      simpa only [rawPrincipalTimeJet_zero, rawFirstTimeJet_zero,
        rawZeroTimeJet_zero, iteratedDeriv_zero, rawLowerFormOperator] using
        (rawVectorGeneratorTimeJet_pairing F hab hJ hK η hη 0 s z (w s)).symm))
  · exact ht

end PoincareConjecture.M35.Uniqueness.Heat
