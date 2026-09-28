import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawMixedCoefficientJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousTimeJetBootstrap
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawGeneratorTimeJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialCoefficientBound
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.RawUniformRestart









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckDomainRegularityNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem raw_compact_heat_spatial_jets_continuous {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (W : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hW : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t)
    (heq : ∀ t ∈ Ioo a b, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (deriv W t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection t) hK.isClosed η hη (W t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη) z (W t))
    (s j : ℕ) (k : Fin n) :
    HasContinuousInteriorJets K (fun t : Ioo a b => iteratedDeriv j W t k) (s + 1) := by
  let A := fun l (t : Ioo a b) => rawPrincipalTimeJet F hab hJ η hη l t
  let B := fun l (t : Ioo a b) => rawFirstTimeJet F hab hJ η hη l t
  let C := fun l (t : Ioo a b) => rawZeroTimeJet F hab hJ η hη l t
  let u := fun l (t : Ioo a b) => iteratedDeriv l W t
  have hu (l : ℕ) (i : Fin n) : Continuous (fun t : Ioo a b => u l t i) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => dirichletForm K) i).contDiff.contDiffAt.comp
      (t : ℝ) (contDiffAt_iteratedDeriv_infty (hW t t.property) l)
    exact hd.continuousAt.comp continuous_subtype_val.continuousAt
  have hAc (l : ℕ) (i j : Fin n) (w : List (Fin n)) : Continuous (fun t : Ioo a b =>
      schwartzMultiplier (orderedSchwartzDerivative w (A l t i j))) :=
    ((contDiffOn_rawPrincipal_mixed_multiplier F hab hJ η hη l i j w).continuousOn.mono
      Ioo_subset_Icc_self).domRestrict
  have hBc (l : ℕ) (i j q : Fin n) (w : List (Fin n)) : Continuous (fun t : Ioo a b =>
      schwartzMultiplier (orderedSchwartzDerivative w (B l t i j q))) :=
    ((contDiffOn_rawFirst_mixed_multiplier F hab hJ η hη l i j q w).continuousOn.mono
      Ioo_subset_Icc_self).domRestrict
  have hCc (l : ℕ) (i j : Fin n) (w : List (Fin n)) : Continuous (fun t : Ioo a b =>
      schwartzMultiplier (orderedSchwartzDerivative w (C l t i j))) :=
    ((contDiffOn_rawZero_mixed_multiplier F hab hJ η hη l i j w).continuousOn.mono
      Ioo_subset_Icc_self).domRestrict
  have hcommuted (l : ℕ) (t : Ioo a b) (z : PiLp 2 (fun _ : Fin n => dirichletForm K)) :
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (u (l + 1) t)) =
      ∑ p ∈ Finset.antidiagonal l, (l.choose p.1 : ℝ) *
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (dirichletVectorLowerOrder hK.isClosed (B p.1 t) (C p.1 t) (u p.2 t)) -
            principalVectorEnergy K (A p.1 t) z (u p.2 t)) := by
    have h := congrArg (fun q : PiLp 2 (fun _ : Fin n => dirichletForm K) => inner ℝ z q)
      (raw_compact_heat_timeJet_equation F hab hJ hK.isClosed η hη W hW heq l t.property)
    simpa only [ContinuousLinearMap.adjoint_inner_right, timeOperatorJet, inner_sum,
      inner_smul_right_eq_smul, nsmul_eq_mul, rawVectorGeneratorTimeJet_pairing, A, B, C, u] using h
  obtain ⟨ell, hell, hEll⟩ := ValueInitial.exists_raw_slab_cutoff_ellipticity
    F isCompact_Icc hJ hK η hη hηK
  obtain ⟨D, hD, hAD⟩ := exists_rawPrincipal_slab_derivative_bound
    F isCompact_Icc hJ η hη
  exact continuous_timeJet_elliptic_bootstrap hK A B C u hu hAc hBc hCc
    (fun t => rawCutoffPrincipalCoefficient_symmetric (F.metric t) η hη) hell hD
    (fun t => hEll t (Ioo_subset_Icc_self t.property))
    (fun t => hAD t (Ioo_subset_Icc_self t.property)) hcommuted s j k

end PoincareConjecture.M35.Uniqueness.Heat
