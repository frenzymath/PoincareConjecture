import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakProduct

open Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

def HasSpatialL2Jet {n : ℕ} (U : Set (Spacetime n)) : ℕ → (Spacetime n → ℝ) → Prop
  | 0, u => MemLp u 2 (volume.restrict U)
  | k + 1, u => MemLp u 2 (volume.restrict U) ∧
      ∃ g : Fin n → Spacetime n → ℝ,
        (∀ i, HasSpatialL2Jet U k (g i)) ∧
        ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ U →
          (∫ y in U, φ y * g i y) = -(∫ y in U, spatialDeriv i φ y * u y)

theorem HasSpatialL2Jet.memLp
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) : MemLp u 2 (volume.restrict U) := by
  cases k with
  | zero => exact hu
  | succ k => exact hu.1

theorem HasSpatialL2Jet.locallyIntegrableOn
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) : LocallyIntegrableOn u U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hu.memLp.locallyIntegrable (by norm_num))

private theorem jet_test_integrable
    {n : ℕ} {U : Set (Spacetime n)} {u φ : Spacetime n → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun y => φ y * u y) (volume.restrict U) := by
  have hul := locallyIntegrableOn_of_locallyIntegrable_restrict
    (hu.locallyIntegrable (by norm_num))
  have hi : Integrable (fun y => φ y * u y) := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left φ u).trans (subset_tsupport φ))).mp
    exact (hul.integrableOn_compact_subset hφU hφc).continuousOn_mul
      hφ.continuous.continuousOn hφc
  exact hi.integrableOn

theorem HasSpatialL2Jet.restrict
    {n k : ℕ} {U V : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hVU : V ⊆ U) : HasSpatialL2Jet V k u := by
  induction k generalizing u with
  | zero => exact hu.mono_measure (Measure.restrict_mono hVU le_rfl)
  | succ k ih =>
    obtain ⟨hum, g, hg, hweak⟩ := hu
    refine ⟨hum.mono_measure (Measure.restrict_mono hVU le_rfl), g, fun i => ih (hg i), ?_⟩
    intro i φ hφ hφc hφV
    have hpair {ψ : Spacetime n → ℝ} (hψ : tsupport ψ ⊆ V)
        (a : Spacetime n → ℝ) : (∫ y in V, ψ y * a y) = ∫ y in U, ψ y * a y := by
      calc
        _ = ∫ y, ψ y * a y := setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ h)), zero_mul])
        _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hVU (hψ h))), zero_mul])).symm
    rw [hpair hφV, hpair (ψ := spatialDeriv i φ)
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans hφV)]
    exact hweak i φ hφ hφc (hφV.trans hVU)

theorem HasSpatialL2Jet.lower
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U (k + 1) u) : HasSpatialL2Jet U k u := by
  induction k generalizing u with
  | zero => exact hu.1
  | succ k ih =>
    obtain ⟨hum, g, hg, hweak⟩ := hu
    exact ⟨hum, g, fun i => ih (hg i), hweak⟩

theorem HasSpatialL2Jet.of_le
    {n j k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hjk : j ≤ k) : HasSpatialL2Jet U j u := by
  induction k generalizing j u with
  | zero =>
    have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
    subst j
    exact hu
  | succ k ih =>
    by_cases he : j = k + 1
    · simpa only [he] using hu
    · exact ih hu.lower (by omega)

theorem HasSpatialL2Jet.zero
    {n : ℕ} (U : Set (Spacetime n)) (k : ℕ) :
    HasSpatialL2Jet U k (fun _ => 0) := by
  induction k with
  | zero => exact MemLp.zero
  | succ k ih =>
    refine ⟨MemLp.zero, fun _ _ => 0, fun _ => ih, ?_⟩
    intro i φ hφ hφc hφU
    simp

theorem HasSpatialL2Jet.add
    {n k : ℕ} {U : Set (Spacetime n)} {u w : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hw : HasSpatialL2Jet U k w) :
    HasSpatialL2Jet U k (fun y => u y + w y) := by
  induction k generalizing u w with
  | zero => exact MemLp.add hu hw
  | succ k ih =>
    obtain ⟨hum, g, hg, hgw⟩ := hu
    obtain ⟨hwm, d, hd, hdw⟩ := hw
    refine ⟨hum.add hwm, fun i y => g i y + d i y, fun i => ih (hg i) (hd i), ?_⟩
    intro i φ hφ hφc hφU
    have hDφ : ContDiff ℝ ∞ (spatialDeriv i φ) :=
      (hφ.fderiv_right (by simp)).clm_apply contDiff_const
    have hDφc : HasCompactSupport (spatialDeriv i φ) := hφc.fderiv_apply ℝ _
    have hDφU : tsupport (spatialDeriv i φ) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans hφU
    simp only [mul_add]
    rw [integral_add (jet_test_integrable (hg i).memLp hφ hφc hφU)
        (jet_test_integrable (hd i).memLp hφ hφc hφU),
      integral_add (jet_test_integrable hum hDφ hDφc hDφU)
        (jet_test_integrable hwm hDφ hDφc hDφU),
      hgw i φ hφ hφc hφU, hdw i φ hφ hφc hφU]
    ring

theorem HasSpatialL2Jet.neg
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) : HasSpatialL2Jet U k (fun y => -u y) := by
  induction k generalizing u with
  | zero => exact MemLp.neg hu
  | succ k ih =>
    obtain ⟨hum, g, hg, hweak⟩ := hu
    refine ⟨hum.neg, fun i y => -g i y, fun i => ih (hg i), ?_⟩
    intro i φ hφ hφc hφU
    simp only [mul_neg, integral_neg, neg_neg]
    linarith only [hweak i φ hφ hφc hφU]

theorem HasSpatialL2Jet.sub
    {n k : ℕ} {U : Set (Spacetime n)} {u w : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hw : HasSpatialL2Jet U k w) :
    HasSpatialL2Jet U k (fun y => u y - w y) := by
  simpa only [sub_eq_add_neg] using hu.add hw.neg

theorem HasSpatialL2Jet.sum
    {n k : ℕ} {U : Set (Spacetime n)} {ι : Type*} (s : Finset ι)
    {f : ι → Spacetime n → ℝ} (hf : ∀ i ∈ s, HasSpatialL2Jet U k (f i)) :
    HasSpatialL2Jet U k (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasSpatialL2Jet.zero U k
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem HasSpatialL2Jet.mul_smooth
    {n k : ℕ} {U : Set (Spacetime n)} {u q : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hU : IsOpen U)
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    HasSpatialL2Jet U k (fun y => q y * u y) := by
  induction k generalizing u q with
  | zero =>
    exact hu.mul' (hq.continuous.memLp_top_of_hasCompactSupport hqc (volume.restrict U))
  | succ k ih =>
    have hulower := hu.lower
    obtain ⟨hum, g, hg, hweak⟩ := hu
    have hDq (i : Fin n) : ContDiff ℝ ∞ (spatialDeriv i q) :=
      (hq.fderiv_right (by simp)).clm_apply contDiff_const
    have hDqc (i : Fin n) : HasCompactSupport (spatialDeriv i q) := hqc.fderiv_apply ℝ _
    refine ⟨hum.mul' (hq.continuous.memLp_top_of_hasCompactSupport hqc (volume.restrict U)),
      fun i y => spatialDeriv i q y * u y + q y * g i y,
      fun i => (ih hulower (hDq i) (hDqc i)).add (ih (hg i) hq hqc), ?_⟩
    intro i φ hφ hφc hφU
    exact (weak_directional_derivative_mul_smooth hU hq (spatialDirection i)
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hum.locallyIntegrable (by norm_num)))
      (hg i).locallyIntegrableOn (hweak i)).2.2 φ hφ hφc hφU

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
