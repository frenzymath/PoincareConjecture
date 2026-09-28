import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoefficientTimeJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem contDiffOn_supported_schwartzMultiplier
    {a b : ℝ} (hab : a < b) (A : ℝ → 𝓢(X, ℝ))
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × X => A p.1 p.2) (Icc a b ×ˢ univ))
    {S : Set X} (hS : IsCompact S) (hsupport : ∀ t ∈ Icc a b, tsupport (A t) ⊆ S) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier (A t)) (Icc a b) := by
  obtain ⟨R, hR, hb⟩ := hS.isBounded.exists_pos_norm_le
  let bump : ContDiffBump (0 : X) := ⟨R, R + 1, hR, by linarith⟩
  let ζ : 𝓢(X, ℝ) := bump.hasCompactSupport.toSchwartzMap bump.contDiff
  have hζ (x : X) (hx : x ∈ S) : ζ x = 1 := by
    apply bump.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb x hx
  have hbound : ∀ f : 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ x, ‖f x‖ ≤ M) → ‖schwartzMultiplierLinear f‖ ≤ 1 * M := by
    intro f M hM hf
    change ‖schwartzMultiplier f‖ ≤ 1 * M
    rw [one_mul]
    exact ContinuousLinearMap.opNorm_le_bound _ hM (fun u => norm_schwartzMultiplier_le f u hf)
  apply contDiffOn_actual_cutoff_operator schwartzMultiplierLinear zero_le_one hbound
    hab (fun p => A p.1 p.2) hA ζ bump.hasCompactSupport A
  intro t ht x
  by_cases hx : x ∈ S
  · rw [hζ x hx, one_mul]
  · have hz : A t x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hx' => hx (hsupport t ht hx'))
    rw [hz, mul_zero]

theorem contDiffOn_supported_lineDeriv_multiplier
    {a b : ℝ} (hab : a < b) (A : ℝ → 𝓢(X, ℝ))
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × X => A p.1 p.2) (Icc a b ×ˢ univ))
    {S : Set X} (hS : IsCompact S) (hsupport : ∀ t ∈ Icc a b, tsupport (A t) ⊆ S)
    (v : X) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier (∂_{v} (A t))) (Icc a b) := by
  apply contDiffOn_supported_schwartzMultiplier hab (fun t => ∂_{v} (A t)) ?_ hS
    (fun t ht => (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (hsupport t ht))
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
    (raw_family_spatial_fderiv_contDiffOn (f := fun t x => A t x) hA).clm_apply
      (contDiffOn_const (c := v))

theorem rawCutoffPrincipalCoefficient_joint_contDiffOn {J : Set ℝ} (F : RicciFlow n X J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × X =>
      rawCutoffPrincipalCoefficient (F.metric p.1) η hη i j p.2) (J ×ˢ univ) := by
  simpa only [rawCutoffPrincipalCoefficient_apply, Function.comp_apply] using!
    (η.smooth'.comp_contDiffOn contDiffOn_snd).mul
      (raw_inverseGram_entry_family_contDiffOn F i j)

theorem rawCutoffPrincipalCoefficient_tsupport {J : Set ℝ} (F : RicciFlow n X J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (t : ℝ) (i j : Fin n) :
    tsupport (rawCutoffPrincipalCoefficient (F.metric t) η hη i j) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_tsupport η
  intro hz
  exact hx (by rw [rawCutoffPrincipalCoefficient_apply, hz, zero_mul])

theorem contDiffOn_rawPrincipal_spatial_multiplier
    {J : Set ℝ} (F : RicciFlow n X J) {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (i j k : Fin n) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier (∂_{EuclideanSpace.single k (1 : ℝ)}
      (rawCutoffPrincipalCoefficient (F.metric t) η hη i j))) (Icc a b) :=
  contDiffOn_supported_lineDeriv_multiplier hab _
    ((rawCutoffPrincipalCoefficient_joint_contDiffOn F η hη i j).mono
      (prod_mono hJ Subset.rfl)) hη
    (fun t _ => rawCutoffPrincipalCoefficient_tsupport F η hη t i j) _

end PoincareConjecture.M35.Uniqueness.Heat
