




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialJetMollification
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakCommutation











open Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical



def HasTimeSpatialL2Jet {n : ℕ} (U : Set (Spacetime n)) :
    ℕ → ℕ → (Spacetime n → ℝ) → Prop
  | 0, k, u => HasSpatialL2Jet U k u
  | m + 1, k, u => HasSpatialL2Jet U k u ∧
      ∃ T : Spacetime n → ℝ, HasTimeSpatialL2Jet U m k T ∧
        ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ U →
          (∫ y in U, φ y * T y) = -(∫ y in U, timeDeriv φ y * u y)


theorem HasTimeSpatialL2Jet.spatial
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) : HasSpatialL2Jet U k u := by
  cases m with
  | zero => exact hu
  | succ m => exact hu.1


theorem HasTimeSpatialL2Jet.memLp
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) : MemLp u 2 (volume.restrict U) :=
  hu.spatial.memLp


theorem HasTimeSpatialL2Jet.locallyIntegrableOn
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) : LocallyIntegrableOn u U volume :=
  hu.spatial.locallyIntegrableOn


theorem HasTimeSpatialL2Jet.congr_ae
    {n m k : ℕ} {U : Set (Spacetime n)} {u v : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (huv : u =ᵐ[volume.restrict U] v) :
    HasTimeSpatialL2Jet U m k v := by
  cases m with
  | zero => exact HasSpatialL2Jet.congr_ae hu huv
  | succ m =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    refine ⟨hus.congr_ae huv, T, hT, ?_⟩
    intro φ hφ hφc hφU
    rw [hTw φ hφ hφc hφU]
    congr 1
    exact integral_congr_ae (huv.mono fun y hy =>
      congrArg (fun a => timeDeriv φ y * a) hy)


theorem HasTimeSpatialL2Jet.restrict
    {n m k : ℕ} {U V : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (hVU : V ⊆ U) :
    HasTimeSpatialL2Jet V m k u := by
  induction m generalizing u with
  | zero => exact HasSpatialL2Jet.restrict hu hVU
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    refine ⟨hus.restrict hVU, T, ih hT, ?_⟩
    intro φ hφ hφc hφV
    have hpair {ψ : Spacetime n → ℝ} (hψ : tsupport ψ ⊆ V)
        (a : Spacetime n → ℝ) : (∫ y in V, ψ y * a y) = ∫ y in U, ψ y * a y := by
      calc
        _ = ∫ y, ψ y * a y := setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ h)), zero_mul])
        _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hVU (hψ h))), zero_mul])).symm
    rw [hpair hφV, hpair (ψ := timeDeriv φ)
      ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hφV)]
    exact hTw φ hφ hφc (hφV.trans hVU)


theorem HasTimeSpatialL2Jet.lower_spatial
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m (k + 1) u) : HasTimeSpatialL2Jet U m k u := by
  induction m generalizing u with
  | zero => exact hu.lower
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    exact ⟨hus.lower, T, ih hT, hTw⟩


theorem HasTimeSpatialL2Jet.of_spatial_le
    {n m j k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (hjk : j ≤ k) :
    HasTimeSpatialL2Jet U m j u := by
  induction m generalizing u with
  | zero => exact hu.of_le hjk
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    exact ⟨hus.of_le hjk, T, ih hT, hTw⟩


theorem HasTimeSpatialL2Jet.lower_time
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U (m + 1) k u) : HasTimeSpatialL2Jet U m k u := by
  induction m generalizing u with
  | zero => exact hu.1
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    exact ⟨hus, T, ih hT, hTw⟩


theorem HasTimeSpatialL2Jet.of_time_le
    {n j m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (hjm : j ≤ m) :
    HasTimeSpatialL2Jet U j k u := by
  induction m generalizing j u with
  | zero =>
    have hj : j = 0 := Nat.eq_zero_of_le_zero hjm
    subst j
    exact hu
  | succ m ih =>
    by_cases hj : j = m + 1
    · simpa only [hj] using hu
    · exact ih hu.lower_time (by omega)

private theorem time_jet_test_integrable
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


theorem HasTimeSpatialL2Jet.zero
    {n : ℕ} (U : Set (Spacetime n)) (m k : ℕ) :
    HasTimeSpatialL2Jet U m k (fun _ => 0) := by
  induction m with
  | zero => exact HasSpatialL2Jet.zero U k
  | succ m ih =>
    refine ⟨HasSpatialL2Jet.zero U k, fun _ => 0, ih, ?_⟩
    intro φ hφ hφc hφU
    simp


theorem HasTimeSpatialL2Jet.add
    {n m k : ℕ} {U : Set (Spacetime n)} {u w : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (hw : HasTimeSpatialL2Jet U m k w) :
    HasTimeSpatialL2Jet U m k (fun y => u y + w y) := by
  induction m generalizing u w with
  | zero => exact HasSpatialL2Jet.add hu hw
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    obtain ⟨hws, S, hS, hSw⟩ := hw
    refine ⟨hus.add hws, fun y => T y + S y, ih hT hS, ?_⟩
    intro φ hφ hφc hφU
    have hDφ : ContDiff ℝ ∞ (timeDeriv φ) :=
      (hφ.fderiv_right (by simp)).clm_apply contDiff_const
    have hDφc : HasCompactSupport (timeDeriv φ) := hφc.fderiv_apply ℝ _
    have hDφU : tsupport (timeDeriv φ) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ (0, 1)).trans hφU
    simp only [mul_add]
    rw [integral_add (time_jet_test_integrable hT.memLp hφ hφc hφU)
        (time_jet_test_integrable hS.memLp hφ hφc hφU),
      integral_add (time_jet_test_integrable hus.memLp hDφ hDφc hDφU)
        (time_jet_test_integrable hws.memLp hDφ hDφc hDφU),
      hTw φ hφ hφc hφU, hSw φ hφ hφc hφU]
    ring


theorem HasTimeSpatialL2Jet.neg
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) : HasTimeSpatialL2Jet U m k (fun y => -u y) := by
  induction m generalizing u with
  | zero => exact HasSpatialL2Jet.neg hu
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    refine ⟨hus.neg, fun y => -T y, ih hT, ?_⟩
    intro φ hφ hφc hφU
    simp only [mul_neg, integral_neg, neg_neg]
    linarith only [hTw φ hφ hφc hφU]


theorem HasTimeSpatialL2Jet.sub
    {n m k : ℕ} {U : Set (Spacetime n)} {u w : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (hw : HasTimeSpatialL2Jet U m k w) :
    HasTimeSpatialL2Jet U m k (fun y => u y - w y) := by
  simpa only [sub_eq_add_neg] using hu.add hw.neg


theorem HasTimeSpatialL2Jet.sum
    {n m k : ℕ} {U : Set (Spacetime n)} {ι : Type*} (s : Finset ι)
    {f : ι → Spacetime n → ℝ} (hf : ∀ i ∈ s, HasTimeSpatialL2Jet U m k (f i)) :
    HasTimeSpatialL2Jet U m k (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasTimeSpatialL2Jet.zero U m k
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))


theorem HasTimeSpatialL2Jet.mul_smooth
    {n m k : ℕ} {U : Set (Spacetime n)} {u q : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m k u) (hU : IsOpen U)
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    HasTimeSpatialL2Jet U m k (fun y => q y * u y) := by
  induction m generalizing u q with
  | zero => exact HasSpatialL2Jet.mul_smooth hu hU hq hqc
  | succ m ih =>
    have hulower := hu.lower_time
    obtain ⟨hus, T, hT, hTw⟩ := hu
    have hDq : ContDiff ℝ ∞ (timeDeriv q) :=
      (hq.fderiv_right (by simp)).clm_apply contDiff_const
    have hDqc : HasCompactSupport (timeDeriv q) := hqc.fderiv_apply ℝ _
    refine ⟨hus.mul_smooth hU hq hqc,
      fun y => timeDeriv q y * u y + q y * T y,
      (ih hulower hDq hDqc).add (ih hT hq hqc), ?_⟩
    intro φ hφ hφc hφU
    exact (weak_directional_derivative_mul_smooth hU hq (0, 1)
      hus.locallyIntegrableOn hT.locallyIntegrableOn hTw).2.2 φ hφ hφc hφU



theorem HasTimeSpatialL2Jet.exists_spatial_derivatives
    {n m k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasTimeSpatialL2Jet U m (k + 1) u) (hU : IsOpen U) :
    ∃ g : Fin n → Spacetime n → ℝ,
      (∀ i, HasTimeSpatialL2Jet U m k (g i)) ∧
      ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        (∫ y in U, φ y * g i y) = -(∫ y in U, spatialDeriv i φ y * u y) := by
  induction m generalizing u with
  | zero => exact hu.2
  | succ m ih =>
    obtain ⟨hus, T, hT, hTw⟩ := hu
    obtain ⟨hum, g, hg, hgw⟩ := hus
    obtain ⟨d, hd, hdw⟩ := ih hT
    refine ⟨g, ?_, hgw⟩
    intro i
    refine ⟨hg i, d i, hd i, ?_⟩
    intro φ hφ hφc hφU
    exact weak_directional_derivative_comm hU (0, 1) (spatialDirection i)
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hum.locallyIntegrable (by norm_num)))
      hT.locallyIntegrableOn (hg i).locallyIntegrableOn (hd i).locallyIntegrableOn
      hTw (hgw i) (hdw i) hφ hφc hφU

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
