import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawGeneratorTimeJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeJetEllipticBootstrap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem raw_compact_heat_all_spatial_jets {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hw : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ w t)
    (heq : ∀ t ∈ Ioo a b, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (deriv w t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection t) hK.isClosed η hη (w t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη) z (w t))
    {t : ℝ} (ht : t ∈ Ioo a b) (s j : ℕ) (k : Fin n) :
    HasInteriorWeakJets K (iteratedDeriv j w t k) (s + 1) := by
  let A := fun l => rawPrincipalTimeJet F hab hJ η hη l t
  let B := fun l => rawFirstTimeJet F hab hJ η hη l t
  let C := fun l => rawZeroTimeJet F hab hJ η hη l t
  let u := fun l => iteratedDeriv l w t
  have hcommuted (l : ℕ) (z : PiLp 2 (fun _ : Fin n => dirichletForm K)) :
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (u (l + 1))) =
      ∑ p ∈ Finset.antidiagonal l, (l.choose p.1 : ℝ) *
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (dirichletVectorLowerOrder hK.isClosed (B p.1) (C p.1) (u p.2)) -
            principalVectorEnergy K (A p.1) z (u p.2)) := by
    have h := congrArg (fun q : PiLp 2 (fun _ : Fin n => dirichletForm K) => inner ℝ z q)
      (raw_compact_heat_timeJet_equation F hab hJ hK.isClosed η hη w hw heq l ht)
    simpa only [ContinuousLinearMap.adjoint_inner_right, timeOperatorJet, inner_sum,
      inner_smul_right_eq_smul, nsmul_eq_mul, rawVectorGeneratorTimeJet_pairing, A, B, C, u] using h
  obtain ⟨ell, hell, hEll⟩ := exists_rawCutoffPrincipalCoefficient_ellipticity
    (F.metric t) hK η hη hηK
  exact timeJet_elliptic_bootstrap hK A B C u
    (rawCutoffPrincipalCoefficient_symmetric (F.metric t) η hη) hell hEll hcommuted s j k

end PoincareConjecture.M35.Uniqueness.Heat
