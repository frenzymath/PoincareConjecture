import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormOperatorTimeJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

def rawPrincipalTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η)
    (k : ℕ) (t : ℝ) (i j : Fin n) : 𝓢(X, ℝ) :=
  cutoffTimeJet (uniqueDiffOn_Icc hab)
    (fun p : ℝ × X => (rawCoordinateGram (F.metric p.1) p.2)⁻¹ i j)
    ((raw_inverseGram_entry_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη i j) k t

def rawFirstTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η)
    (k : ℕ) (t : ℝ) (i j l : Fin n) : 𝓢(X, ℝ) :=
  cutoffTimeJet (uniqueDiffOn_Icc hab)
    (fun p : ℝ × X => rawFirstComponent (F.connection p.1) i j l p.2)
    ((rawFirstComponent_family_contDiffOn F i j l).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffFirstComponent (F.connection r) η hη i j l) k t

def rawZeroTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η)
    (k : ℕ) (t : ℝ) (i j : Fin n) : 𝓢(X, ℝ) :=
  cutoffTimeJet (uniqueDiffOn_Icc hab)
    (fun p : ℝ × X => rawZeroComponent (F.connection p.1) i j p.2)
    ((rawZeroComponent_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffZeroComponent (F.connection r) η hη i j) k t

@[simp] theorem rawPrincipalTimeJet_zero {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (t : ℝ) :
    rawPrincipalTimeJet F hab hJ η hη 0 t = rawCutoffPrincipalCoefficient (F.metric t) η hη := rfl

@[simp] theorem rawFirstTimeJet_zero {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (t : ℝ) :
    rawFirstTimeJet F hab hJ η hη 0 t = rawCutoffFirstComponent (F.connection t) η hη := rfl

@[simp] theorem rawZeroTimeJet_zero {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (t : ℝ) :
    rawZeroTimeJet F hab hJ η hη 0 t = rawCutoffZeroComponent (F.connection t) η hη := rfl

theorem hasDerivWithinAt_rawPrincipalTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (i j : Fin n)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => schwartzMultiplier (rawPrincipalTimeJet F hab hJ η hη k r i j))
      (schwartzMultiplier (rawPrincipalTimeJet F hab hJ η hη (k + 1) t i j)) (Icc a b) t :=
  hasDerivWithinAt_cutoffTimeJet_multiplier hab _
    ((raw_inverseGram_entry_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη i j)
    (fun _ _ _ => rfl) k ht

theorem hasDerivWithinAt_rawFirstTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set X)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (i j l : Fin n)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt
      (fun r => dirichletValueMultiplier K (rawFirstTimeJet F hab hJ η hη k r i j l))
      (dirichletValueMultiplier K (rawFirstTimeJet F hab hJ η hη (k + 1) t i j l)) (Icc a b) t :=
  hasDerivWithinAt_cutoffTimeJet_value_multiplier K hab _
    ((rawFirstComponent_family_contDiffOn F i j l).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffFirstComponent (F.connection r) η hη i j l)
    (fun _ _ _ => rfl) k ht

theorem hasDerivWithinAt_rawZeroTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set X)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (i j : Fin n)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => dirichletValueMultiplier K (rawZeroTimeJet F hab hJ η hη k r i j))
      (dirichletValueMultiplier K (rawZeroTimeJet F hab hJ η hη (k + 1) t i j)) (Icc a b) t :=
  hasDerivWithinAt_cutoffTimeJet_value_multiplier K hab _
    ((rawZeroComponent_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffZeroComponent (F.connection r) η hη i j)
    (fun _ _ _ => rfl) k ht

theorem hasDerivWithinAt_rawPrincipalFormTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set X)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => principalFormOperator K (rawPrincipalTimeJet F hab hJ η hη k r))
      (principalFormOperator K (rawPrincipalTimeJet F hab hJ η hη (k + 1) t)) (Icc a b) t :=
  hasDerivWithinAt_principalFormOperator K _ _ (fun i j =>
    hasDerivWithinAt_rawPrincipalTimeJet F hab hJ η hη k i j ht)

theorem hasDerivWithinAt_rawLowerFormTimeJet {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsClosed K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => dirichletVectorLowerOrder hK
      (rawFirstTimeJet F hab hJ η hη k r) (rawZeroTimeJet F hab hJ η hη k r))
      (dirichletVectorLowerOrder hK (rawFirstTimeJet F hab hJ η hη (k + 1) t)
        (rawZeroTimeJet F hab hJ η hη (k + 1) t)) (Icc a b) t :=
  hasDerivWithinAt_dirichletVectorLowerOrder hK _ _ _ _
    (fun i j l => hasDerivWithinAt_rawFirstTimeJet F hab hJ K η hη k i j l ht)
    (fun i j => hasDerivWithinAt_rawZeroTimeJet F hab hJ K η hη k i j ht)

end PoincareConjecture.M35.Uniqueness.Heat
