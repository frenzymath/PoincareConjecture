/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Sobolev/Manifold/EmbeddingSubcritical.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development. The local file extracts a subset of the upstream development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Density

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal ContDiff

namespace Poincare.Analysis.Sobolev.EuclideanEmbedding

namespace EuclideanSubcritical

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma eq_zero_off_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN} (hf_supp : tsupport f ⊆ Ω)
    {x : EuN} (hx : x ∉ Ω) : f x = 0 := by
  have hx_notsupp : x ∉ tsupport f := fun h => hx (hf_supp h)
  exact image_eq_zero_of_notMem_tsupport hx_notsupp

omit [NeZero d] in
private lemma fderiv_eq_zero_off_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN}
    (hf_supp : tsupport f ⊆ Ω)
    {x : EuN} (hx : x ∉ Ω) : fderiv ℝ f x = 0 := by
  have hx_notsupp : x ∉ tsupport f := fun h => hx (hf_supp h)
  have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds hx_notsupp
  have hf_zero : f =ᶠ[𝓝 x] (fun _ : EuN => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem h_nhds ?_
    intro y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [Filter.EventuallyEq.fderiv_eq hf_zero]
  simp

omit [NeZero d] in
private lemma eLpNorm_eq_eLpNorm_restrict_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN} (hΩ_meas : MeasurableSet Ω)
    (hf_supp : tsupport f ⊆ Ω) (p : ℝ≥0∞) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict Ω) := by
  have h_eq : f = Ω.indicator f := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact eq_zero_off_of_tsupport_subset hf_supp hx
  calc eLpNorm f p volume
      = eLpNorm (Ω.indicator f) p volume := by rw [← h_eq]
    _ = eLpNorm f p (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

omit [NeZero d] in
private lemma eLpNorm_fderiv_eq_eLpNorm_fderiv_restrict_of_tsupport_subset
    {f : EuN → ℝ} {Ω : Set EuN}
    (hΩ_meas : MeasurableSet Ω) (hf_supp : tsupport f ⊆ Ω) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ f) p volume = eLpNorm (fderiv ℝ f) p (volume.restrict Ω) := by
  have h_eq : fderiv ℝ f = Ω.indicator (fderiv ℝ f) := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact fderiv_eq_zero_off_of_tsupport_subset hf_supp hx
  calc eLpNorm (fderiv ℝ f) p volume
      = eLpNorm (Ω.indicator (fderiv ℝ f)) p volume := by rw [← h_eq]
    _ = eLpNorm (fderiv ℝ f) p (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := volume) (p := p) (f := fderiv ℝ f) (s := Ω) hΩ_meas

omit [NeZero d] in
private lemma classical_partial_ae_eq_chosenWeakPartial_of_smooth
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) (i : Fin d) :
    (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω := by
  have hf_mem : Poincare.Analysis.Sobolev.Euclidean.MemWkp (d := d) 1 p f Ω :=
    Poincare.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := d) hΩ_open hf_smooth hf_compact hf_supp hp_one 1
  have hf_W1p : Poincare.Analysis.Sobolev.Weak.MemW1p (d := d) p f Ω :=
    Poincare.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) i
        (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω :=
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) i
        (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω) f Ω :=
    Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
      (volume.restrict Ω) :=
    (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hf_W1p i).locallyIntegrable hp_one
  exact Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

omit [NeZero d] in
private lemma norm_fderiv_le_sum_norm_partials
    (f : EuN → ℝ) (x : EuN) :
    ‖fderiv ℝ f x‖ ≤ ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ := by
  classical
  set v : EuN := (InnerProductSpace.toDual ℝ EuN).symm (fderiv ℝ f x) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuN) v = fderiv ℝ f x := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ f x‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2 (fun i : Fin d => (fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1))) i := by simp
  have h_v_sum :
      v = ∑ i : Fin d, EuclideanSpace.single i ((fderiv ℝ f x) (EuclideanSpace.single i 1)) := by
    ext j
    rw [h_v_eq_components]
    simp [Finset.sum_apply]
  rw [h_fderiv_norm_eq_v, h_v_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

omit [NeZero d] in
private lemma eLpNorm_fderiv_le_sum_eLpNorm_partials
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {μ : Measure EuN}
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    eLpNorm (fderiv ℝ f) p μ ≤
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p μ := by
  classical
  have h_aesm_comp : ∀ i : Fin d,
      AEStronglyMeasurable
        (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous (fun x : EuN => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ x : EuN,
      ‖fderiv ℝ f x‖ ≤ ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ :=
    fun x => norm_fderiv_le_sum_norm_partials (d := d) f x
  have h_step1 : eLpNorm (fderiv ℝ f) p μ
      = eLpNorm (fun x => ‖fderiv ℝ f x‖) p μ := (eLpNorm_norm _).symm
  rw [h_step1]
  have h_step2 : eLpNorm (fun x : EuN => ‖fderiv ℝ f x‖) p μ ≤
      eLpNorm
        (fun x : EuN => ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) p μ := by
    apply eLpNorm_mono_real
    intro x
    have h := h_pt x
    have h_norm : ‖‖fderiv ℝ f x‖‖ = ‖fderiv ℝ f x‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact h
  refine h_step2.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := p)
    (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => fun x : EuN => ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hp_one
  have h_lhs_eq :
      (fun x : EuN => ∑ i : Fin d, ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin d, fun x : EuN => ‖(fderiv ℝ f x) (EuclideanSpace.single i 1)‖ := by
    funext x
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

omit [NeZero d] in
private lemma eLpNorm_classical_partial_eq_chosen
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) (i : Fin d) :
    eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p (volume.restrict Ω)
      = eLpNorm
          (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
          p (volume.restrict Ω) :=
  eLpNorm_congr_ae
    (classical_partial_ae_eq_chosenWeakPartial_of_smooth
      (d := d) hp_one hΩ_open hf_smooth hf_compact hf_supp i)

private lemma eLpNorm_fderiv_smooth_le_d_mul_wkpNorm
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) :
    eLpNorm (fderiv ℝ f) p (volume.restrict Ω) ≤
      (d : ℝ≥0∞) *
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f
          Ω := by
  classical
  have h_grad_le := eLpNorm_fderiv_le_sum_eLpNorm_partials (d := d) hp_one
    (μ := volume.restrict Ω) hf_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin d,
      eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p (volume.restrict Ω)
        = eLpNorm
            (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
            p (volume.restrict Ω) := fun i =>
    eLpNorm_classical_partial_eq_chosen (d := d) hp_one hΩ_open hf_smooth hf_compact hf_supp i
  have h_step1 :
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) p (volume.restrict Ω)
        = ∑ i : Fin d,
          eLpNorm
            (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
            p (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin d,
            eLpNorm
              (Poincare.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := d) p j β f Ω)
              p (volume.restrict Ω) :=
    Poincare.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 p f Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin d,
          eLpNorm
            (Poincare.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := d) p 1 β f Ω) p (volume.restrict Ω)) =
        ∑ i : Fin d,
          eLpNorm
            (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
            p (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin d,
        eLpNorm
          (Poincare.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := d) p 1 β f Ω) p (volume.restrict Ω) =
          eLpNorm
            (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p (β 0) f Ω)
            p (volume.restrict Ω) := by
      intro β
      have hit :
          Poincare.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := d) p 1 β f Ω =
            Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p (β 0) f Ω := by
        rw [Poincare.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
        simp [Poincare.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin d) ≃ Fin d :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p (β 0) f Ω)
          p (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
          p (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin d,
          eLpNorm
            (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
            p (volume.restrict Ω)) ≤
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f
          Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < d := NeZero.pos d
  have hd_one_le : (1 : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by exact_mod_cast hd_pos
  conv_lhs => rw [show Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := d) 1 p f Ω = 1 *
    Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p f Ω from
    (one_mul _).symm]
  gcongr

private lemma sobolev_smooth_compactSupport_in_Ω
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {φ : EuN → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Ω) :
    eLpNorm φ
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict Ω) ≤
      ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) *
        eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) (volume.restrict Ω) := by
  have h_lhs_eq :
      eLpNorm φ
          (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) volume =
        eLpNorm φ
          (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict Ω) :=
    eLpNorm_eq_eLpNorm_restrict_of_tsupport_subset (d := d)
      hΩ_open.measurableSet hφ_supp _
  have h_rhs_eq :
      eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) volume =
        eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) (volume.restrict Ω) :=
    eLpNorm_fderiv_eq_eLpNorm_fderiv_restrict_of_tsupport_subset (d := d)
      hΩ_open.measurableSet hφ_supp _
  have h_smooth_sob := Poincare.Analysis.Sobolev.Weak.sobolev_smooth (d := d) hp_one hp_dim
    (hφ_smooth.of_le (by norm_cast)) hφ_compact
  rw [← h_lhs_eq, ← h_rhs_eq]
  exact h_smooth_sob

theorem eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ}
    (hf : Poincare.Analysis.Sobolev.Euclidean.MemWkp (d := d)
      1 (ENNReal.ofReal p) f Ω)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) :
    eLpNorm f
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) (volume.restrict Ω) ≤
      ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) * (d : ℝ≥0∞) *
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d)
          1 (ENNReal.ofReal p) f Ω := by
  classical
  set p_enn : ℝ≥0∞ := ENNReal.ofReal p with hp_enn_def
  set p_star_real : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_star_real_def
  set p_star : ℝ≥0∞ := ENNReal.ofReal p_star_real with hp_star_def
  have hp_pos : 0 < p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : p_enn ≠ ⊤ := by rw [hp_enn_def]; exact ENNReal.ofReal_ne_top
  have hp_star_pos : 0 < p_star_real := by
    rw [hp_star_real_def]
    apply div_pos
    · exact mul_pos (by exact_mod_cast (NeZero.pos d)) hp_pos
    · linarith
  have hp_enn_ne_zero : p_enn ≠ 0 := by
    rw [hp_enn_def]; exact ENNReal.ofReal_ne_zero_iff.mpr hp_pos
  have h_pick : ∀ n : ℕ, ∃ φ : EuN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ x) Ω ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have h_eps_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      apply div_pos one_pos
      exact_mod_cast Nat.succ_pos n
    exact Poincare.Analysis.Sobolev.Euclidean.MemWkp.exists_smooth_compactSupport_approx
      (d := d) hΩ_open 1 p_enn hp_enn_one hp_enn_top hf hf_compact hf_supp
      (1 / (n + 1 : ℝ)) h_eps_pos
  set φ : ℕ → EuN → ℝ := fun n => (h_pick n).choose with hφ_def
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := fun n => (h_pick n).choose_spec.1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := fun n => (h_pick n).choose_spec.2.1
  have hφ_supp : ∀ n, tsupport (φ n) ⊆ Ω := fun n => (h_pick n).choose_spec.2.2.1
  have hφ_close : ∀ n,
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ n x) Ω ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) :=
    fun n => (h_pick n).choose_spec.2.2.2
  have h_smooth_sob : ∀ n,
      eLpNorm (φ n) p_star (volume.restrict Ω) ≤
        ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) *
          eLpNorm (fderiv ℝ (φ n)) p_enn (volume.restrict Ω) := fun n =>
    sobolev_smooth_compactSupport_in_Ω (d := d) hp_one hp_dim hΩ_open
      (hφ_smooth n) (hφ_compact n) (hφ_supp n)
  have h_grad_bound : ∀ n,
      eLpNorm (fderiv ℝ (φ n)) p_enn (volume.restrict Ω) ≤
        (d : ℝ≥0∞) *
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (φ n) Ω :=
    fun n => eLpNorm_fderiv_smooth_le_d_mul_wkpNorm
      (d := d) (p := p_enn) hp_enn_one hΩ_open (hφ_smooth n) (hφ_compact n) (hφ_supp n)
  have h_φn_mem : ∀ n,
      Poincare.Analysis.Sobolev.Euclidean.MemWkp (d := d)
        1 p_enn (φ n) Ω := fun n =>
    Poincare.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := d) hΩ_open (hφ_smooth n) (hφ_compact n) (hφ_supp n) hp_enn_one 1
  have h_diff_mem : ∀ n,
      Poincare.Analysis.Sobolev.Euclidean.MemWkp (d := d)
        1 p_enn (fun x => f x - φ n x) Ω := fun n =>
    Poincare.Analysis.Sobolev.Euclidean.MemWkp.sub
      (d := d) hp_enn_one hΩ_open hf (h_φn_mem n)
  have h_wkp_φn_le : ∀ n,
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn (φ n)
        Ω ≤
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn f Ω +
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ n x) Ω := by
    intro n
    have h_φn_decomp : (φ n) = (fun x => (φ n x - f x) + f x) := by funext x; ring
    rw [h_φn_decomp]
    have h_v_mem :
        Poincare.Analysis.Sobolev.Euclidean.MemWkp (d := d)
          1 p_enn (fun x => φ n x - f x) Ω :=
      Poincare.Analysis.Sobolev.Euclidean.MemWkp.sub
        (d := d) hp_enn_one hΩ_open (h_φn_mem n) hf
    have h_tri := Poincare.Analysis.Sobolev.Euclidean.wkpNorm_add_le
      (d := d) hp_enn_one hΩ_open h_v_mem hf
    refine h_tri.trans ?_
    have h_neg_eq :
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
            (fun x => φ n x - f x) Ω =
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) 1 p_enn
            (fun x => f x - φ n x) Ω := by
      have h_eq : (fun x : EuN => φ n x - f x) = (fun x : EuN => -(f x - φ n x)) := by
        funext x; ring
      rw [h_eq]
      have h_smul := Poincare.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
        (d := d) hp_enn_one hΩ_open (h_diff_mem n) (-1)
      have h_smul_eq :
          (fun x : EuN => (-1 : ℝ) * (f x - φ n x)) = (fun x : EuN => -(f x - φ n x)) := by
        funext x; ring
      rw [h_smul_eq] at h_smul
      rw [h_smul]
      simp
    rw [h_neg_eq, add_comm]
    have h_simplify : (fun x : EuN => f x - (φ n x - f x + f x)) = (fun x => f x - φ n x) := by
      funext x; ring
    rw [h_simplify]
  have h_eLpNorm_diff_le_wkp : ∀ n,
      eLpNorm (fun x => f x - φ n x) p_enn (volume.restrict Ω) ≤
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ n x) Ω :=
    fun n => by
      simpa only [Poincare.Analysis.Sobolev.Euclidean.wkpNorm_zero] using
        Poincare.Analysis.Sobolev.Euclidean.wkpNorm_mono_order
          (Nat.zero_le 1) (fun x => f x - φ n x) Ω (p := p_enn)
  have h_decay_to_zero : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)))
      atTop (nhds 0) := by
    have hReal : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
        have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact h2.atTop_add tendsto_const_nhds
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hReal
  have h_eLpNorm_diff_to_zero : Tendsto (fun n => eLpNorm
      (fun x => f x - φ n x) p_enn (volume.restrict Ω)) atTop (nhds 0) := by
    have h_total_le : ∀ n,
        eLpNorm (fun x => f x - φ n x) p_enn (volume.restrict Ω) ≤
          ENNReal.ofReal (1 / (n + 1 : ℝ)) := fun n =>
      (h_eLpNorm_diff_le_wkp n).trans (hφ_close n)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_decay_to_zero
      (Filter.Eventually.of_forall (fun _ => zero_le))
      (Filter.Eventually.of_forall h_total_le)
  have hf_aesm : AEStronglyMeasurable f (volume.restrict Ω) := hf.memLp.aestronglyMeasurable
  have hφ_aesm : ∀ n, AEStronglyMeasurable (φ n) (volume.restrict Ω) :=
    fun n => (hφ_smooth n).continuous.aestronglyMeasurable
  have h_tim : TendstoInMeasure (volume.restrict Ω) φ atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm hp_enn_ne_zero hφ_aesm hf_aesm ?_
    have h_neg_eq : ∀ n,
        eLpNorm (fun x => φ n x - f x) p_enn (volume.restrict Ω) =
          eLpNorm (fun x => f x - φ n x) p_enn (volume.restrict Ω) := by
      intro n
      have h_eq : (fun x : EuN => φ n x - f x) = (fun x : EuN => -(f x - φ n x)) := by
        funext x; ring
      rw [h_eq]
      have h_neg_apply : (fun x : EuN => -(f x - φ n x)) = -(fun x : EuN => f x - φ n x) := by
        funext x; rfl
      rw [h_neg_apply, eLpNorm_neg]
    refine (Filter.tendsto_congr h_neg_eq).mpr h_eLpNorm_diff_to_zero
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := h_tim.exists_seq_tendsto_ae
  have h_aesm_subseq : ∀ n, AEStronglyMeasurable (φ (σ n)) (volume.restrict Ω) :=
    fun n => hφ_aesm (σ n)
  have h_fatou : eLpNorm f p_star (volume.restrict Ω) ≤
      atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star (volume.restrict Ω)) :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm h_aesm_subseq f hσ_ae
  set C : ℝ≥0∞ := ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) * (d : ℝ≥0∞) with hC_def
  set N : ℝ≥0∞ := Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := d) 1 p_enn f Ω with hN_def
  have h_per_n : ∀ n,
      eLpNorm (φ (σ n)) p_star (volume.restrict Ω) ≤
        C *
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (φ (σ n)) Ω := by
    intro n
    have h1 := h_smooth_sob (σ n)
    have h2 := h_grad_bound (σ n)
    calc eLpNorm (φ (σ n)) p_star (volume.restrict Ω)
        ≤ ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) *
            eLpNorm (fderiv ℝ (φ (σ n))) p_enn (volume.restrict Ω) := h1
      _ ≤ ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) *
            ((d : ℝ≥0∞) *
              Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := d) 1 p_enn (φ (σ n)) Ω) := by gcongr
      _ = C *
            Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := d) 1 p_enn (φ (σ n)) Ω := by rw [hC_def]; ring
  have h_wkp_subseq : ∀ n,
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (φ (σ n)) Ω ≤ N +
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω :=
    fun n => h_wkp_φn_le (σ n)
  have h_per_n_v2 : ∀ n,
      eLpNorm (φ (σ n)) p_star (volume.restrict Ω) ≤
        C * (N +
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) := fun n =>
    (h_per_n n).trans (by gcongr; exact h_wkp_subseq n)
  have h_liminf_le_C_lim :
      atTop.liminf (fun n => eLpNorm (φ (σ n)) p_star (volume.restrict Ω))
      ≤ atTop.liminf (fun n => C * (N +
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω)) := by
    refine Filter.liminf_le_liminf (Filter.Eventually.of_forall h_per_n_v2) ?_ ?_
    · exact isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall (fun _ => zero_le))
    · exact isCoboundedUnder_ge_of_eventually_le atTop
        (Filter.Eventually.of_forall (fun _ => le_top))
  have h_wkp_diff_decay : Tendsto (fun n =>
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ n x) Ω) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_decay_to_zero
      (Filter.Eventually.of_forall (fun _ => zero_le))
      (Filter.Eventually.of_forall hφ_close)
  have h_wkp_diff_subseq_decay : Tendsto (fun n =>
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) atTop (nhds 0) :=
    h_wkp_diff_decay.comp hσ_mono.tendsto_atTop
  have hC_ne_top : C ≠ ⊤ := by
    rw [hC_def]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  have h_C_diff_decay : Tendsto (fun n => C *
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) atTop (nhds 0) := by
    simpa using
      (ENNReal.Tendsto.const_mul h_wkp_diff_subseq_decay (Or.inr hC_ne_top))
  have h_alg : (fun n => C * (N +
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω)) =
      (fun n => C * N + C *
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) := by
    funext n
    rw [mul_add]
  rw [h_alg] at h_liminf_le_C_lim
  have h_liminf_const_add :
      atTop.liminf (fun n => C * N + C *
          Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω)
        = C * N := by
    rw [show (fun n => C * N + C *
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) =
      (fun _ => C * N) + (fun n => C *
        Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := d) 1 p_enn (fun x => f x - φ (σ n) x) Ω) by rfl]
    rw [ENNReal.liminf_add_of_right_tendsto_zero h_C_diff_decay]
    simp
  rw [h_liminf_const_add] at h_liminf_le_C_lim
  exact h_fatou.trans h_liminf_le_C_lim

end EuclideanSubcritical

end Poincare.Analysis.Sobolev.EuclideanEmbedding
