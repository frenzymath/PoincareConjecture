
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Region
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace



namespace Poincare.HamiltonIvey

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem mem_region_iff_rayleigh (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) (A : E →ₗ[ℝ] E) :
    A ∈ region hn t ↔ A.IsSymmetric ∧
      ∀ v : E, ‖v‖ = 1 →
        (LinearMap.trace ℝ E A, max (-inner ℝ v (A v)) 0) ∈ scalarRegion t := by
  constructor
  · rintro ⟨hA, hmem⟩
    refine ⟨hA, fun v hv => scalarRegion_downward ht hmem ?_⟩
    exact max_le_max (neg_le_neg (rayleigh_ge_least hA hn hv)) le_rfl
  · rintro ⟨hA, hmem⟩
    refine ⟨hA, ?_⟩
    have h := hmem (hA.eigenvectorBasis hn 2) ((hA.eigenvectorBasis hn).orthonormal.1 2)
    simpa [hA.apply_eigenvectorBasis hn, inner_smul_right,
      (hA.eigenvectorBasis hn).orthonormal.1 2] using h

theorem region_zero_mem (hn : Module.finrank ℝ E = 3) {t : ℝ} (ht : 0 ≤ t) :
    (0 : E →ₗ[ℝ] E) ∈ region hn t := by
  refine ⟨LinearMap.IsSymmetric.zero, ?_⟩
  let hzero : (0 : E →ₗ[ℝ] E).IsSymmetric := LinearMap.IsSymmetric.zero
  have heig : hzero.eigenvalues hn 2 = 0 := by
    have hev := hzero.hasEigenvalue_eigenvalues hn 2
    rw [Module.End.hasEigenvalue_iff] at hev
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hev
    rw [Module.End.eigenspace_def, LinearMap.mem_ker] at hv
    have hv' : hzero.eigenvalues hn 2 = 0 ∨ v = 0 := by
      simpa [hzero] using hv
    exact hv'.resolve_right hv0
  change ((LinearMap.trace ℝ E) 0, max (-hzero.eigenvalues hn 2) 0) ∈ scalarRegion t
  rw [show (LinearMap.trace ℝ E) 0 = 0 by simp, heig]
  rw [mem_scalarRegion_iff ht]
  rw [show max (-0 : ℝ) 0 = 0 by norm_num]
  rw [clippedBarrier, max_eq_left (cutoff_pos ht).le,
    logBarrier_cutoff ht]
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)

theorem region_nonempty (hn : Module.finrank ℝ E = 3) {t : ℝ} (ht : 0 ≤ t) :
    (region hn t).Nonempty := ⟨0, region_zero_mem hn ht⟩

theorem clippedBarrier_scale {t X : ℝ} (ht : 0 ≤ t) :
    clippedBarrier 0 ((1 + t) * X) = (1 + t) * clippedBarrier t X := by
  have hc : 0 < 1 + t := by linarith
  have hcut : cutoff 0 = (1 + t) * cutoff t := by
    simp [cutoff]
    field_simp
  rw [clippedBarrier, clippedBarrier, hcut]
  have hmax : max ((1 + t) * cutoff t) ((1 + t) * X) =
      (1 + t) * max (cutoff t) X := by
    apply le_antisymm
    · apply max_le
      · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt hc)
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hc)
    · rcases le_total (cutoff t) X with h | h
      · rw [max_eq_right h]
        exact le_max_right _ _
      · rw [max_eq_left h]
        exact le_max_left _ _
  rw [hmax]
  have hpos : 0 < max (cutoff t) X := (cutoff_pos ht).trans_le (le_max_left _ _)
  have hscaled : logBarrier 0 ((1 + t) * max (cutoff t) X) =
      (1 + t) * logBarrier t (max (cutoff t) X) := by
    have h := logBarrier_div ht
      (show 0 < (1 + t) * max (cutoff t) X by positivity)
      (x := (1 + t) * max (cutoff t) X)
    field_simp at h ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm
  rw [hscaled]

theorem scalarRegion_scale_iff {t S X : ℝ} (ht : 0 ≤ t) :
    (S, X) ∈ scalarRegion t ↔
      ((1 + t) * S, (1 + t) * X) ∈ scalarRegion 0 := by
  rw [mem_scalarRegion_iff ht, mem_scalarRegion_iff (by norm_num)]
  rw [clippedBarrier_scale ht]
  constructor <;> intro h <;> nlinarith [show 0 < 1 + t by linarith]

theorem continuousOn_clippedBarrier :
    ContinuousOn (fun p : ℝ × ℝ => clippedBarrier p.1 p.2)
      {p | 0 ≤ p.1} := by
  have hden : ∀ p : ℝ × ℝ, p ∈ {p | 0 ≤ p.1} → 1 + p.1 ≠ 0 := by
    intro p hp
    dsimp at hp
    linarith
  have hcut : ContinuousOn (fun p : ℝ × ℝ => cutoff p.1) {p | 0 ≤ p.1} :=
    continuousOn_const.div (continuousOn_const.add continuousOn_fst) hden
  have hmax : ContinuousOn (fun p : ℝ × ℝ => max (cutoff p.1) p.2) {p | 0 ≤ p.1} :=
    fun p hp => (hcut p hp).max (continuousOn_snd p hp)
  have hlog := (continuousOn_const.add continuousOn_fst).log hden
  convert (Real.continuous_mul_log.comp_continuousOn hmax).add
    (hmax.mul (hlog.sub (continuousOn_const (c := (3 : ℝ))))) using 1
  ext p
  dsimp [clippedBarrier, logBarrier]
  ring

theorem continuous_clippedBarrier {t : ℝ} (ht : 0 ≤ t) :
    Continuous (clippedBarrier t) := by
  exact continuousOn_clippedBarrier.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ht)

theorem continuous_operatorTrace :
    Continuous (fun A : E →L[ℝ] E => LinearMap.trace ℝ E A.toLinearMap) := by
  exact ((LinearMap.trace ℝ E).comp
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).symm.toLinearMap
    ).continuous_of_finiteDimensional

omit [FiniteDimensional ℝ E] in
theorem isClosed_symmetric_continuousLinearMap :
    IsClosed {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric} := by
  simp only [LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe, Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun w =>
    isClosed_eq ((ContinuousLinearMap.apply ℝ E v).continuous.inner
      (continuous_const : Continuous (fun _ : E →L[ℝ] E => w)))
      ((continuous_const : Continuous (fun _ : E →L[ℝ] E => v)).inner
        (ContinuousLinearMap.apply ℝ E w).continuous)


def continuousRegion (hn : Module.finrank ℝ E = 3) (t : ℝ) :
    Set (E →L[ℝ] E) := {A | A.toLinearMap ∈ region hn t}

@[simp] theorem mem_continuousRegion (hn : Module.finrank ℝ E = 3)
    (t : ℝ) (A : E →L[ℝ] E) :
    A ∈ continuousRegion hn t ↔ A.toLinearMap ∈ region hn t := Iff.rfl

@[simp] theorem toContinuousLinearMap_mem_continuousRegion
    (hn : Module.finrank ℝ E = 3) (t : ℝ) (A : E →ₗ[ℝ] E) :
    A.toContinuousLinearMap ∈ continuousRegion hn t ↔ A ∈ region hn t := Iff.rfl

theorem continuousRegion_nonempty (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : (continuousRegion hn t).Nonempty :=
  ⟨0, region_zero_mem hn ht⟩

theorem isClosed_continuousRegion (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : IsClosed (continuousRegion hn t) := by
  have heq : continuousRegion hn t =
      {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric ∧
        ∀ v : E, ‖v‖ = 1 →
          clippedBarrier t (max (-inner ℝ v (A v)) 0) ≤ LinearMap.trace ℝ E A.toLinearMap} := by
    ext A
    simp only [mem_continuousRegion, mem_region_iff_rayleigh hn ht,
      mem_ofPred_eq, mem_scalarRegion_iff ht, ContinuousLinearMap.coe_coe]
  rw [heq, ofPred_and]
  simp only [ofPred_forall]
  refine isClosed_symmetric_continuousLinearMap.inter
    (isClosed_iInter fun v => isClosed_iInter fun _ => ?_)
  exact isClosed_le ((continuous_clippedBarrier ht).comp
    ((continuous_const.inner (ContinuousLinearMap.apply ℝ E v).continuous).neg.max
      continuous_const)) continuous_operatorTrace

theorem isClosed_continuousRegion_spacetime (hn : Module.finrank ℝ E = 3) :
    IsClosed {p : ℝ × (E →L[ℝ] E) | 0 ≤ p.1 ∧ p.2 ∈ continuousRegion hn p.1} := by
  let S : Set (ℝ × (E →L[ℝ] E)) := {p | 0 ≤ p.1}
  have hS : IsClosed S := isClosed_le continuous_const continuous_fst
  have heq : {p : ℝ × (E →L[ℝ] E) | 0 ≤ p.1 ∧ p.2 ∈ continuousRegion hn p.1} =
      S ∩ {p | p.2.toLinearMap.IsSymmetric} ∩
        {p | ∀ v : E, ‖v‖ = 1 → p ∈ S ∧
          clippedBarrier p.1 (max (-inner ℝ v (p.2 v)) 0) ≤
            LinearMap.trace ℝ E p.2.toLinearMap} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨ht, hA⟩
      obtain ⟨hs, hA⟩ := (mem_region_iff_rayleigh hn ht p.2.toLinearMap).mp hA
      exact ⟨⟨ht, hs⟩, fun v hv => ⟨ht, (mem_scalarRegion_iff ht).mp (hA v hv)⟩⟩
    · rintro ⟨⟨ht, hs⟩, hA⟩
      exact ⟨ht, (mem_region_iff_rayleigh hn ht p.2.toLinearMap).mpr
        ⟨hs, fun v hv => (mem_scalarRegion_iff ht).mpr (hA v hv).2⟩⟩
  rw [heq]
  simp only [ofPred_forall]
  refine (hS.inter (isClosed_symmetric_continuousLinearMap.preimage continuous_snd)).inter
    (isClosed_iInter fun v => isClosed_iInter fun _ => ?_)
  apply hS.isClosed_le _ (continuous_operatorTrace.comp continuous_snd).continuousOn
  exact continuousOn_clippedBarrier.comp
    (continuous_fst.prodMk
      ((continuous_const.inner ((ContinuousLinearMap.apply ℝ E v).continuous.comp
        continuous_snd)).neg.max continuous_const)).continuousOn
    (fun p hp => hp)


theorem region_conj_equiv_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hn : Module.finrank ℝ E = 3)
    (hm : Module.finrank ℝ F = 3) (e : E ≃ₗᵢ[ℝ] F)
    {t : ℝ} (ht : 0 ≤ t) (A : E →ₗ[ℝ] E) :
    e.toLinearEquiv.conj A ∈ region hm t ↔ A ∈ region hn t := by
  rw [mem_region_iff_rayleigh hm ht, mem_region_iff_rayleigh hn ht]
  have hsymm : (e.toLinearEquiv.conj A).IsSymmetric ↔ A.IsSymmetric :=
    LinearMap.isSymmetric_linearIsometryEquiv_conj_iff A e
  rw [hsymm, LinearMap.trace_conj']
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h v hv
    simpa [LinearEquiv.conj_apply] using h (e v) (by simpa using hv)
  · intro h v hv
    simpa [LinearEquiv.conj_apply, LinearIsometryEquiv.inner_map_eq_flip] using
      h (e.symm v) (by simpa using hv)

theorem region_conj_iff (hn : Module.finrank ℝ E = 3)
    (e : E ≃ₗᵢ[ℝ] E) {t : ℝ} (ht : 0 ≤ t) (A : E →ₗ[ℝ] E) :
    e.toLinearEquiv.conj A ∈ region hn t ↔ A ∈ region hn t :=
  region_conj_equiv_iff hn hn e ht A

theorem region_scale_iff (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) (A : E →ₗ[ℝ] E) :
    A ∈ region hn t ↔ (1 + t) • A ∈ region hn 0 := by
  have hc : 0 < 1 + t := by linarith
  have hsymm : ((1 + t) • A).IsSymmetric ↔ A.IsSymmetric := by
    constructor
    · intro h v w
      have h' := h v w
      simpa only [LinearMap.smul_apply, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real, mul_eq_mul_left_iff, hc.ne', or_false] using h'
    · exact fun h => h.smul (by simp)
  rw [mem_region_iff_rayleigh hn ht, mem_region_iff_rayleigh hn (by norm_num), hsymm]
  refine and_congr_right fun _ => forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [scalarRegion_scale_iff ht]
  simp only [map_smul, smul_eq_mul, LinearMap.smul_apply, inner_smul_right,
    ← mul_neg, mul_max_of_nonneg _ _ hc.le, mul_zero]

theorem convex_continuousRegion (hn : Module.finrank ℝ E = 3)
    {t : ℝ} (ht : 0 ≤ t) : Convex ℝ (continuousRegion hn t) := by
  intro A hA B hB a b ha hb hab
  exact convex_region hn ht hA hB ha hb hab

end Poincare.HamiltonIvey
