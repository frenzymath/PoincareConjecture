/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Copyright 2026 Scott Armstrong and Julia Kempe
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Sobolev/Tools/DifferenceQuotientWeakLimitLoc.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Additional source: https://github.com/scottnarmstrong/DeGiorgi
DeGiorgi/SobolevSpace/Approximation.lean
Comparison revision: 4c1b3077d3782b24065184df4ba59501b2e56fc7.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development. The local file extracts a subset of the upstream development.
DeGiorgi material was incorporated through DifferentialGeometry.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace Poincare.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem exists_smooth_cutoff
    {K Ω' : Set E} (hK : IsCompact K) (hΩ' : IsOpen Ω') (hKΩ' : K ⊆ Ω') :
    ∃ η : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ K, η x = 1) ∧
      tsupport η ⊆ Ω' := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ' hKΩ'
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E) (s := Metric.thickening δ K) (t := K)
      isOpen_thickening hK.isClosed (self_subset_thickening hδ_pos K) with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, ?_⟩
  · apply HasCompactSupport.intro' (K := Metric.cthickening δ K)
    · exact hK.cthickening (r := δ)
    · simpa using (isClosed_cthickening : IsClosed (Metric.cthickening δ K))
    · intro x hx
      have hxt : x ∉ tsupport η := by
        intro hxt
        have hx_closure : x ∈ closure (Metric.thickening δ K) := by
          rw [tsupport, hη_support] at hxt
          exact hxt
        exact hx ((Metric.closure_thickening_subset_cthickening δ K) hx_closure)
      exact image_eq_zero_of_notMem_tsupport hxt
  · intro x hx
    exact (hη_one_iff x).1 hx
  · rw [tsupport, hη_support]
    exact (Metric.closure_thickening_subset_cthickening δ K).trans hδΩ

omit [NeZero d] in
private lemma smoothCSSupportedIn_zero_mem (Ω'' : Set E) :
    ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ) ∧
      HasCompactSupport (0 : E → ℝ) ∧
      tsupport (0 : E → ℝ) ⊆ Ω'' := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  have h_supp : Function.support (0 : E → ℝ) = ∅ := by
    ext x; simp
  rw [tsupport, h_supp, closure_empty]
  exact empty_subset _

omit [NeZero d] in
private lemma smoothCSSupportedIn_add_mem
    {Ω'' : Set E}
    {φ ψ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω'')
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω'') :
    ContDiff ℝ (⊤ : ℕ∞) (φ + ψ) ∧
      HasCompactSupport (φ + ψ) ∧
      tsupport (φ + ψ) ⊆ Ω'' := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  refine subset_trans (tsupport_add (f := φ) (g := ψ)) ?_
  exact union_subset hφ.2.2 hψ.2.2

omit [NeZero d] in
private lemma smoothCSSupportedIn_smul_mem
    {Ω'' : Set E}
    (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω'') :
    ContDiff ℝ (⊤ : ℕ∞) (c • φ) ∧
      HasCompactSupport (c • φ) ∧
      tsupport (c • φ) ⊆ Ω'' := by
  refine ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left, ?_⟩
  refine subset_trans ?_ hφ.2.2
  have hsubset : Function.support (c • φ) ⊆ Function.support φ := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hφx
    apply hx
    change c • φ x = 0
    rw [hφx]; simp
  exact closure_mono hsubset

def smoothCSSupportedInSubmodule (Ω'' : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ω''}
  add_mem' := fun hφ hψ => smoothCSSupportedIn_add_mem (Ω'' := Ω'') hφ hψ
  zero_mem' := smoothCSSupportedIn_zero_mem (Ω'' := Ω'')
  smul_mem' := fun c _ hφ => smoothCSSupportedIn_smul_mem (Ω'' := Ω'') c hφ

omit [NeZero d] in
@[simp] lemma mem_smoothCSSupportedInSubmodule {Ω'' : Set E} {φ : E → ℝ} :
    φ ∈ (smoothCSSupportedInSubmodule (d := d) Ω'') ↔
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω'' :=
  Iff.rfl

omit [NeZero d] in
lemma memLp_two_restrict_of_smoothCS
    {Ω'' : Set E}
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ) :
    MemLp φ 2 ((volume : Measure E).restrict Ω'') :=
  (hφ.continuous.memLp_of_hasCompactSupport hφ_supp).restrict _

def smoothCSSupportedInToLp (Ω'' : Set E) :
    smoothCSSupportedInSubmodule (d := d) Ω'' →ₗ[ℝ]
      Lp ℝ 2 ((volume : Measure E).restrict Ω'') where
  toFun φ :=
    (memLp_two_restrict_of_smoothCS (d := d) (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1
  map_add' φ ψ := by
    refine Lp.ext ?_
    have h1 : ⇑((memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') (φ + ψ).2.1 (φ + ψ).2.2.1).toLp ((φ + ψ).1)) =ᵐ[
          (volume : Measure E).restrict Ω''] (φ + ψ).1 :=
      MemLp.coeFn_toLp _
    have h2 : ⇑((memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1 +
        (memLp_two_restrict_of_smoothCS (d := d)
          (Ω'' := Ω'') ψ.2.1 ψ.2.2.1).toLp ψ.1) =ᵐ[
          (volume : Measure E).restrict Ω'']
          ⇑((memLp_two_restrict_of_smoothCS (d := d)
              (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) +
            ⇑((memLp_two_restrict_of_smoothCS (d := d)
              (Ω'' := Ω'') ψ.2.1 ψ.2.2.1).toLp ψ.1) :=
      Lp.coeFn_add _ _
    have h3 : ⇑((memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) =ᵐ[
          (volume : Measure E).restrict Ω''] φ.1 :=
      MemLp.coeFn_toLp _
    have h4 : ⇑((memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') ψ.2.1 ψ.2.2.1).toLp ψ.1) =ᵐ[
          (volume : Measure E).restrict Ω''] ψ.1 :=
      MemLp.coeFn_toLp _
    have h_add_coe : ((φ + ψ :
        (smoothCSSupportedInSubmodule (d := d) Ω'')).1 : E → ℝ) =
        φ.1 + ψ.1 := rfl
    refine h1.trans ?_
    refine (h2.trans ?_).symm
    rw [h_add_coe]
    filter_upwards [h3, h4] with x hx3 hx4
    simp only [Pi.add_apply]
    rw [hx3, hx4]
  map_smul' c φ := by
    refine Lp.ext ?_
    have h1 : ⇑((memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') (c • φ).2.1 (c • φ).2.2.1).toLp
          ((c • φ).1)) =ᵐ[(volume : Measure E).restrict Ω''] (c • φ).1 :=
      MemLp.coeFn_toLp _
    have h2 : ⇑(c • (memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1)
        =ᵐ[(volume : Measure E).restrict Ω'']
          c • ⇑((memLp_two_restrict_of_smoothCS (d := d)
            (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) :=
      Lp.coeFn_smul c _
    have h3 : ⇑((memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) =ᵐ[
          (volume : Measure E).restrict Ω''] φ.1 :=
      MemLp.coeFn_toLp _
    have h_smul_coe : ((c • φ :
        (smoothCSSupportedInSubmodule (d := d) Ω'')).1 : E → ℝ) =
        c • φ.1 := rfl
    refine h1.trans ?_
    rw [h_smul_coe]
    have h_id_eq :
        (RingHom.id ℝ) c • (memLp_two_restrict_of_smoothCS (d := d)
            (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1
          = c • (memLp_two_restrict_of_smoothCS (d := d)
            (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1 := rfl
    rw [show ⇑((RingHom.id ℝ) c •
        (memLp_two_restrict_of_smoothCS (d := d)
          (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) =
        ⇑(c • (memLp_two_restrict_of_smoothCS (d := d)
          (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) from by
      rw [h_id_eq]]
    filter_upwards [h2, h3] with x hx2 hx3
    rw [hx2, Pi.smul_apply, Pi.smul_apply, hx3]

omit [NeZero d] in
@[simp] lemma smoothCSSupportedInToLp_apply
    (Ω'' : Set E) (φ : smoothCSSupportedInSubmodule (d := d) Ω'') :
    smoothCSSupportedInToLp (d := d) Ω'' φ =
      (memLp_two_restrict_of_smoothCS (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1 := rfl

omit [NeZero d] in
lemma denseRange_smoothCSSupportedInToLp
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    DenseRange (smoothCSSupportedInToLp (d := d) Ω'') := by
  classical
  have hΩ''_meas : MeasurableSet Ω'' := hΩ''_open.measurableSet
  have : IsFiniteMeasure ((volume : Measure E).restrict Ω'') := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_of_le_of_lt (measure_mono subset_closure)
      hΩ''_compact_closure.measure_lt_top
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  set ε' : ℝ := ε / 4 with hε'_def
  have hε' : 0 < ε' := by rw [hε'_def]; linarith
  obtain ⟨g₀, hg₀_cs, hg₀_smooth, hg₀_close⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := (volume : Measure E).restrict Ω'')
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.memLp f) hε'
  obtain ⟨B, hB⟩ :=
    hg₀_smooth.continuous.bounded_above_of_compact_support hg₀_cs
  set Bp : ℝ := max B 0 + 1 with hBp_def
  have hBp_pos : 0 < Bp := by
    rw [hBp_def]; have := le_max_right B 0; linarith
  have hBp_nn : 0 ≤ Bp := hBp_pos.le
  set δ : ℝ := (ε' / Bp) ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have : 0 < ε' / Bp := div_pos hε' hBp_pos
    positivity
  have hδ_ennreal_pos : 0 < ENNReal.ofReal δ := by
    rwa [ENNReal.ofReal_pos]
  have hK_exists :
      ∃ K : Set E, IsCompact K ∧ K ⊆ Ω'' ∧
        ((volume : Measure E).restrict Ω'') (Ω'' \ K) ≤ ENNReal.ofReal δ := by
    have h_meas_full : ((volume : Measure E).restrict Ω'') Ω'' < ⊤ := by
      rw [Measure.restrict_apply hΩ''_meas, Set.inter_self]
      exact lt_of_le_of_lt (measure_mono subset_closure)
        hΩ''_compact_closure.measure_lt_top
    have h_inner :=
      MeasurableSet.exists_isCompact_lt_add
        (μ := (volume : Measure E).restrict Ω'')
        hΩ''_meas h_meas_full.ne hδ_ennreal_pos.ne'
    obtain ⟨K, hK_sub, hK_compact, hK_lt⟩ := h_inner
    refine ⟨K, hK_compact, hK_sub, ?_⟩
    have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
    have h_diff_meas : MeasurableSet (Ω'' \ K) := hΩ''_meas.diff hK_meas
    have h_disj : Disjoint K (Ω'' \ K) := disjoint_sdiff_self_right
    have h_union : Ω'' = K ∪ (Ω'' \ K) := (Set.union_sdiff_cancel hK_sub).symm
    have h_meas_split :
        ((volume : Measure E).restrict Ω'') Ω'' =
          ((volume : Measure E).restrict Ω'') K +
            ((volume : Measure E).restrict Ω'') (Ω'' \ K) := by
      have h := MeasureTheory.measure_union (μ := (volume : Measure E).restrict Ω'')
        h_disj h_diff_meas
      rw [← h_union] at h
      exact h
    have hK_le : ((volume : Measure E).restrict Ω'') K ≠ ⊤ :=
      ne_top_of_le_ne_top h_meas_full.ne (measure_mono hK_sub)
    have h_le_K_plus_delta :
        ((volume : Measure E).restrict Ω'') Ω'' <
          ((volume : Measure E).restrict Ω'') K + ENNReal.ofReal δ := hK_lt
    rw [h_meas_split] at h_le_K_plus_delta
    have h_eq : ((volume : Measure E).restrict Ω'') K +
            ((volume : Measure E).restrict Ω'') (Ω'' \ K) <
          ((volume : Measure E).restrict Ω'') K + ENNReal.ofReal δ :=
      h_le_K_plus_delta
    exact (ENNReal.add_lt_add_iff_left hK_le).mp h_eq |>.le
  obtain ⟨K, hK_compact, hK_sub, hK_meas_diff⟩ := hK_exists
  obtain ⟨η, hη_smooth, hη_cs, hη_range, hη_one_on_K, hη_tsupp_in⟩ :=
    exists_smooth_cutoff
      (d := d) (K := K) (Ω' := Ω'') hK_compact hΩ''_open hK_sub
  set g : E → ℝ := fun x => η x * g₀ x with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := hη_smooth.mul hg₀_smooth
  have hg_cs : HasCompactSupport g := hη_cs.mul_right
  have hg_tsupp_in_Ω'' : tsupport g ⊆ Ω'' := by
    refine subset_trans ?_ hη_tsupp_in
    have hsupport_sub : Function.support g ⊆ Function.support η := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hηx
      apply hx
      change η x * g₀ x = 0
      rw [hηx]; ring
    exact closure_mono hsupport_sub
  have h_pt_bd : ∀ᵐ x ∂((volume : Measure E).restrict Ω''),
      ‖(g : E → ℝ) x - g₀ x‖ ≤ Bp *
        (Ω'' \ K).indicator (fun _ => (1 : ℝ)) x := by
    rw [ae_restrict_iff' hΩ''_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    by_cases hxK : x ∈ K
    · have hηx : η x = 1 := hη_one_on_K x hxK
      have h_g_eq : g x = g₀ x := by
        change η x * g₀ x = g₀ x; rw [hηx]; ring
      rw [show (g : E → ℝ) x - g₀ x = g₀ x - g₀ x from by
          show g x - g₀ x = g₀ x - g₀ x; rw [h_g_eq]]
      rw [sub_self, norm_zero]
      have hxnotin : x ∉ Ω'' \ K := fun ⟨_, hnotK⟩ => hnotK hxK
      rw [Set.indicator_of_notMem hxnotin]
      simp
    · have h_diff_eq : (g : E → ℝ) x - g₀ x = (η x - 1) * g₀ x := by
        change η x * g₀ x - g₀ x = (η x - 1) * g₀ x; ring
      rw [h_diff_eq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hg₀_bd : |g₀ x| ≤ max B 0 :=
        (le_trans (hB x) (le_max_left _ _))
      have hη_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
      have hη_diff : |η x - 1| ≤ 1 := by
        rcases hη_in with ⟨h1, h2⟩
        have h_le_zero : η x - 1 ≤ 0 := by linarith
        have h_ge_neg1 : -(1 : ℝ) ≤ η x - 1 := by linarith
        rw [abs_of_nonpos h_le_zero]
        linarith
      have hx_in_diff : x ∈ Ω'' \ K := ⟨hx, hxK⟩
      rw [Set.indicator_of_mem hx_in_diff]
      have h_max_pos : 0 ≤ max B 0 := le_max_right _ _
      have h_g0_nn : 0 ≤ |g₀ x| := abs_nonneg _
      calc |η x - 1| * |g₀ x|
          ≤ 1 * (max B 0) := by
            refine mul_le_mul hη_diff hg₀_bd h_g0_nn (by linarith)
        _ = max B 0 := by ring
        _ ≤ Bp * 1 := by rw [hBp_def]; linarith
  have h_meas_diff : MeasurableSet (Ω'' \ K) :=
    hΩ''_meas.diff hK_compact.isClosed.measurableSet
  have h_g_minus_g0_le :
      eLpNorm ((g : E → ℝ) - g₀) 2 ((volume : Measure E).restrict Ω'') ≤
        ENNReal.ofReal Bp *
          (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) := by
    have h_indicator_eLpNorm :
        eLpNorm ((Ω'' \ K).indicator (fun _ : E => Bp)) 2
          ((volume : Measure E).restrict Ω'') =
        ENNReal.ofReal Bp *
          (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) := by
      have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have hp_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [eLpNorm_indicator_const h_meas_diff hp_ne_zero hp_ne_top]
      have h_two_toReal : ((2 : ℝ≥0∞) : ℝ≥0∞).toReal = 2 := by simp
      rw [h_two_toReal]
      rw [Real.enorm_eq_ofReal hBp_nn]
    refine le_trans ?_ (le_of_eq h_indicator_eLpNorm)
    refine eLpNorm_mono_ae ?_
    refine h_pt_bd.mono ?_
    intro x hx
    have h_sub_apply : ((g : E → ℝ) - g₀) x = g x - g₀ x := rfl
    rw [h_sub_apply]
    by_cases hxd : x ∈ Ω'' \ K
    · rw [Set.indicator_of_mem hxd] at hx
      rw [Set.indicator_of_mem hxd]
      rw [Real.norm_eq_abs] at *
      rw [show ‖(Bp : ℝ)‖ = |Bp| from rfl, abs_of_nonneg hBp_nn]
      linarith
    · rw [Set.indicator_of_notMem hxd] at hx
      rw [Set.indicator_of_notMem hxd]
      have h_zero_bd : Bp * 0 = (0 : ℝ) := by ring
      rw [h_zero_bd] at hx
      have h_norm_nn : 0 ≤ ‖g x - g₀ x‖ := norm_nonneg _
      have h_lhs_eq : ‖g x - g₀ x‖ = 0 :=
        le_antisymm hx h_norm_nn
      rw [h_lhs_eq]
      simp
  refine ⟨smoothCSSupportedInToLp (d := d) Ω''
    ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩, ?_, ?_⟩
  · exact ⟨⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩, rfl⟩
  · rw [dist_comm, Lp.dist_def]
    have h_g_eq_ae : ⇑(smoothCSSupportedInToLp (d := d) Ω''
        ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩) =ᵐ[
          (volume : Measure E).restrict Ω''] g := by
      simp only [smoothCSSupportedInToLp_apply]
      exact MemLp.coeFn_toLp _
    have h_eLpNorm_eq :
        eLpNorm (⇑(smoothCSSupportedInToLp (d := d) Ω''
            ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩) - ⇑f) 2
          ((volume : Measure E).restrict Ω'') =
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [h_g_eq_ae] with x hx
      change (⇑(smoothCSSupportedInToLp (d := d) Ω''
          ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩)) x - (⇑f) x =
        g x - (⇑f) x
      rw [hx]
    rw [h_eLpNorm_eq]
    have h_eLpNorm_diff_le :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          eLpNorm ((g : E → ℝ) - g₀) 2 ((volume : Measure E).restrict Ω'') +
            eLpNorm ((g₀ : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') := by
      have h_split : (g : E → ℝ) - ⇑f =
          ((g : E → ℝ) - g₀) + (g₀ - ⇑f) := by
        ext x
        change g x - (⇑f) x = (g x - g₀ x) + (g₀ x - (⇑f) x)
        ring
      rw [h_split]
      have h_aesm₁ : AEStronglyMeasurable ((g : E → ℝ) - g₀)
          ((volume : Measure E).restrict Ω'') :=
        (hg_smooth.continuous.sub hg₀_smooth.continuous).aestronglyMeasurable
      have h_aesm₂ : AEStronglyMeasurable ((g₀ : E → ℝ) - ⇑f)
          ((volume : Measure E).restrict Ω'') := by
        refine hg₀_smooth.continuous.aestronglyMeasurable.sub ?_
        exact (Lp.aestronglyMeasurable f)
      exact eLpNorm_add_le h_aesm₁ h_aesm₂ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_meas_le :
        (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) ≤
          (ENNReal.ofReal δ) ^ ((1 : ℝ) / 2) := by
      refine ENNReal.rpow_le_rpow hK_meas_diff (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h_diff_size :
        eLpNorm ((g : E → ℝ) - g₀) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal ε' := by
      refine le_trans h_g_minus_g0_le ?_
      calc ENNReal.ofReal Bp *
            (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) ≤
          ENNReal.ofReal Bp *
            (ENNReal.ofReal δ) ^ ((1 : ℝ) / 2) := by gcongr
        _ = ENNReal.ofReal (Bp * δ ^ ((1 : ℝ) / 2)) := by
              rw [show (ENNReal.ofReal δ) ^ ((1 : ℝ) / 2) =
                  ENNReal.ofReal (δ ^ ((1 : ℝ) / 2)) from
                ENNReal.ofReal_rpow_of_pos hδ_pos]
              rw [← ENNReal.ofReal_mul hBp_nn]
        _ ≤ ENNReal.ofReal ε' := by
              refine ENNReal.ofReal_le_ofReal ?_
              have h_sqrt : δ ^ ((1 : ℝ) / 2) = ε' / Bp := by
                rw [hδ_def]
                rw [show ((ε' / Bp) ^ 2 : ℝ) = (ε' / Bp) ^ (2 : ℕ) from rfl]
                rw [← Real.rpow_natCast (ε' / Bp) 2]
                have h_pos : 0 < ε' / Bp := div_pos hε' hBp_pos
                rw [← Real.rpow_mul h_pos.le]
                rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num]
                rw [Real.rpow_one]
              rw [h_sqrt]
              rw [show Bp * (ε' / Bp) = ε' from by
                  field_simp]
    have h_g0_close :
        eLpNorm ((g₀ : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal ε' := by
      have hcalc : eLpNorm ((fun x => g₀ x - (⇑f) x)) 2
          ((volume : Measure E).restrict Ω'') =
        eLpNorm ((fun x => (⇑f) x - g₀ x)) 2
          ((volume : Measure E).restrict Ω'') := by
        rw [show (fun x => g₀ x - (⇑f) x) = -(fun x => (⇑f) x - g₀ x) from by
          ext x; simp]
        exact eLpNorm_neg _ _ _
      have h_sub_eq : ((g₀ : E → ℝ) - ⇑f) = fun x => g₀ x - (⇑f) x := rfl
      rw [h_sub_eq, hcalc]
      have h_eq : (fun x => (⇑f) x - g₀ x) = (⇑f - g₀ : E → ℝ) := rfl
      rw [h_eq]
      exact hg₀_close
    have h_total_le :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal ε' + ENNReal.ofReal ε' := by
      refine le_trans h_eLpNorm_diff_le ?_
      exact add_le_add h_diff_size h_g0_close
    have h_total_le_e2 :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal (ε / 2) := by
      refine le_trans h_total_le ?_
      rw [← ENNReal.ofReal_add hε'.le hε'.le]
      have : ε' + ε' = ε / 2 := by rw [hε'_def]; ring
      rw [this]
    have h_eLpNorm_lt_top :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') < ⊤ :=
      lt_of_le_of_lt h_total_le_e2 ENNReal.ofReal_lt_top
    have h_dist_le : (eLpNorm ((g : E → ℝ) - ⇑f) 2
          ((volume : Measure E).restrict Ω'')).toReal ≤ ε / 2 := by
      have := ENNReal.toReal_mono (a := eLpNorm
          ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω''))
        (b := ENNReal.ofReal (ε / 2))
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (ε / 2) ≠ ⊤) h_total_le_e2
      have hε2 : 0 ≤ ε / 2 := by linarith
      rw [ENNReal.toReal_ofReal hε2] at this
      exact this
    linarith

end Poincare.Analysis.Sobolev
