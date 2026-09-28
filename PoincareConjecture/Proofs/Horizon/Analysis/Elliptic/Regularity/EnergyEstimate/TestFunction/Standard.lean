import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Weak

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Poincare.Analysis.Sobolev.NirenbergStandardTest

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

noncomputable def standardNirenbergTest
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) : EuclN → ℝ :=
  diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h u x)

omit [NeZero d] in
theorem standardNirenbergTest_apply
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) (x : EuclN) (hh : h ≠ 0) :
    standardNirenbergTest k h η u x =
      ((η (x + (-h) • EuclideanSpace.single k 1))^2 *
          diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) -
        (η x)^2 * diffQuot k h u x) / (-h) := by
  unfold standardNirenbergTest
  rw [diffQuot_apply_of_ne (d := d) k (neg_ne_zero.mpr hh)]

omit [NeZero d] in
@[simp] lemma standardNirenbergTest_zero_h
    (k : Fin d) (η u : EuclN → ℝ) :
    standardNirenbergTest k 0 η u = 0 := by
  funext x
  unfold standardNirenbergTest
  simp [diffQuot]

omit [NeZero d] in
theorem standardNirenbergTest_support_subset
    (k : Fin d) (h : ℝ) {η : EuclN → ℝ}
    (u : EuclN → ℝ) :
    Function.support (standardNirenbergTest k h η u) ⊆
      tsupport η ∪
        {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hh : h = 0
  · exfalso
    apply hx
    subst hh
    unfold standardNirenbergTest
    simp [diffQuot]
  · have h_apply := standardNirenbergTest_apply (d := d) k h η u x hh
    rw [h_apply] at hx
    have h_num_ne : (η (x + (-h) • EuclideanSpace.single k 1))^2 *
        diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) -
        (η x)^2 * diffQuot k h u x ≠ 0 := by
      intro h_zero
      apply hx
      rw [h_zero, zero_div]
    by_cases hηx : η x = 0
    · right
      have hFx_zero : (η x)^2 * diffQuot k h u x = 0 := by
        rw [show (η x)^2 = 0 from by rw [hηx]; ring, zero_mul]
      rw [hFx_zero, sub_zero] at h_num_ne
      have hηy_ne : η (x + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
        intro h_zero
        apply h_num_ne
        rw [show (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
          rw [h_zero]; ring, zero_mul]
      exact subset_tsupport η hηy_ne
    · left
      exact subset_tsupport η hηx

omit [NeZero d] in
theorem standardNirenbergTest_tsupport_subset
    (k : Fin d) (h : ℝ) {η : EuclN → ℝ}
    (u : EuclN → ℝ) :
    tsupport (standardNirenbergTest k h η u) ⊆
      tsupport η ∪
        {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} := by
  have htrans_cont : Continuous
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_pre_closed : IsClosed
      {x : EuclN | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} :=
    (isClosed_tsupport η).preimage htrans_cont
  have h_rhs_closed : IsClosed
      (tsupport η ∪
        {x : EuclN | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η}) :=
    (isClosed_tsupport η).union h_pre_closed
  refine closure_minimal ?_ h_rhs_closed
  exact standardNirenbergTest_support_subset (d := d) k h u

omit [NeZero d] in
theorem standardNirenbergTest_hasCompactSupport
    (k : Fin d) (h : ℝ) {η : EuclN → ℝ} (hη_cs : HasCompactSupport η)
    (u : EuclN → ℝ) :
    HasCompactSupport (standardNirenbergTest k h η u) := by
  set v : EuclN := (-h) • EuclideanSpace.single k 1 with hv_def
  set htrans_homeo : EuclN ≃ₜ EuclN := Homeomorph.addRight v with htrans_def
  have h_set_eq :
      {x : EuclN | x + v ∈ tsupport η} = htrans_homeo ⁻¹' (tsupport η) := by
    ext x
    simp [htrans_homeo]
  have h_pre_eq :
      htrans_homeo ⁻¹' (tsupport η) = htrans_homeo.symm '' (tsupport η) := by
    ext x
    constructor
    · intro hx
      refine ⟨htrans_homeo x, hx, ?_⟩
      exact htrans_homeo.symm_apply_apply x
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hxy : htrans_homeo x = y := by
        rw [← hyx, htrans_homeo.apply_symm_apply]
      rw [Set.mem_preimage, hxy]
      exact hy
  have h_translated_compact : IsCompact (htrans_homeo ⁻¹' (tsupport η)) := by
    rw [h_pre_eq]
    exact hη_cs.image htrans_homeo.symm.continuous
  have h_union_compact : IsCompact (tsupport η ∪
      {x : EuclN | x + v ∈ tsupport η}) := by
    rw [h_set_eq]
    exact hη_cs.union h_translated_compact
  have h_sub : tsupport (standardNirenbergTest k h η u) ⊆
      tsupport η ∪ {x : EuclN | x + v ∈ tsupport η} :=
    standardNirenbergTest_tsupport_subset (d := d) k h u
  exact h_union_compact.of_isClosed_subset (isClosed_tsupport _) h_sub

omit [NeZero d] in
private lemma locallyIntegrable_diffQuot
    (k : Fin d) (h : ℝ) {u : EuclN → ℝ}
    (hu_locInt : LocallyIntegrable u (volume : Measure EuclN)) :
    LocallyIntegrable (diffQuot k h u) (volume : Measure EuclN) := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    exact locallyIntegrable_const _
  · have h_eq_dq : diffQuot k h u =
        fun x => h⁻¹ * (translate k h u x) + (-h⁻¹) * u x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh u x]
      change (u (x + h • EuclideanSpace.single k 1) - u x) / h =
        h⁻¹ * u (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * u x
      field_simp; ring
    rw [h_eq_dq]
    have hτ_locInt : LocallyIntegrable (translate k h u)
        (volume : Measure EuclN) := by
      have hMP : MeasurePreserving
          (fun x : EuclN => x + h • EuclideanSpace.single k 1)
          volume volume :=
        measurePreserving_add_right volume _
      let τ : EuclN ≃ₜ EuclN :=
        Homeomorph.addRight (h • EuclideanSpace.single k 1)
      have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
      have hMP_τ : MeasurePreserving τ volume volume := by
        rw [show (τ : EuclN → EuclN) =
          fun x => x + h • EuclideanSpace.single k 1 from rfl]
        exact hMP
      intro x
      obtain ⟨V, hV_mem, hf_int⟩ := hu_locInt (τ x)
      refine ⟨τ ⁻¹' V, ?_, ?_⟩
      · exact τ.continuous.continuousAt.preimage_mem_nhds hV_mem
      · have h_eq : translate k h u = u ∘ (τ : EuclN → EuclN) := rfl
        rw [h_eq]
        exact (hMP_τ.integrableOn_comp_preimage hτ_emb (f := u) (s := V)).mpr hf_int
    have h1 : LocallyIntegrable (fun x : EuclN => h⁻¹ * translate k h u x)
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => h⁻¹ * translate k h u x) =
          h⁻¹ • translate k h u := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact hτ_locInt.smul h⁻¹
    have h2 : LocallyIntegrable (fun x : EuclN => (-h⁻¹) * u x)
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => (-h⁻¹) * u x) = (-h⁻¹) • u := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact hu_locInt.smul (-h⁻¹)
    exact h1.add h2

omit [NeZero d] in
private lemma locallyIntegrable_continuous_mul
    {η f : EuclN → ℝ} (hη : Continuous η)
    (hf_locInt : LocallyIntegrable f (volume : Measure EuclN)) :
    LocallyIntegrable (fun x => η x * f x) (volume : Measure EuclN) := by
  rw [← locallyIntegrableOn_univ] at hf_locInt ⊢
  have hcl : IsLocallyClosed (Set.univ : Set EuclN) :=
    isClosed_univ.isLocallyClosed
  exact LocallyIntegrableOn.continuousOn_mul hf_locInt hη.continuousOn hcl

omit [NeZero d] in
private lemma locallyIntegrable_of_restrict_univ
    {f : EuclN → ℝ}
    (hf : LocallyIntegrable f ((volume : Measure EuclN).restrict Set.univ)) :
    LocallyIntegrable f (volume : Measure EuclN) := by
  rwa [Measure.restrict_univ] at hf

omit [NeZero d] in
private lemma locallyIntegrable_to_restrict_univ
    {f : EuclN → ℝ} (hf : LocallyIntegrable f (volume : Measure EuclN)) :
    LocallyIntegrable f ((volume : Measure EuclN).restrict Set.univ) := by
  rwa [Measure.restrict_univ]

omit [NeZero d] in
theorem hasWeakPartialDeriv_standardNirenbergTest
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (diffQuot k (-h)
        (fun y =>
          (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y))
      (standardNirenbergTest k h η u) Set.univ := by
  have hη_cont : Continuous η := hη.continuous
  have hη_sq_cont : Continuous (fun y : EuclN => (η y)^2) := hη_cont.pow 2
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hpartial_η_cont : Continuous
      (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_2η_partial_cont : Continuous
      (fun y : EuclN => 2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη_cont).mul hpartial_η_cont
  have hu_locInt' : LocallyIntegrable u (volume : Measure EuclN) :=
    locallyIntegrable_of_restrict_univ (d := d) hu_locInt
  have hg_j_locInt' : LocallyIntegrable g_j (volume : Measure EuclN) :=
    locallyIntegrable_of_restrict_univ (d := d) hg_j_locInt
  have h_dq_u_locInt : LocallyIntegrable (diffQuot k h u)
      (volume : Measure EuclN) :=
    locallyIntegrable_diffQuot (d := d) k h hu_locInt'
  have h_dq_g_locInt : LocallyIntegrable (diffQuot k h g_j)
      (volume : Measure EuclN) :=
    locallyIntegrable_diffQuot (d := d) k h hg_j_locInt'
  have h_F_locInt : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h u y) (volume : Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) hη_sq_cont h_dq_u_locInt
  have h_F_locInt_restrict : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h u y)
      ((volume : Measure EuclN).restrict Set.univ) :=
    locallyIntegrable_to_restrict_univ (d := d) h_F_locInt
  have h_term1_locInt : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y) (volume : Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) hη_sq_cont h_dq_g_locInt
  have h_term2_locInt : LocallyIntegrable
      (fun y => 2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      (volume : Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) h_2η_partial_cont h_dq_u_locInt
  have h_partial_locInt : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      (volume : Measure EuclN) :=
    h_term1_locInt.add h_term2_locInt
  have h_partial_locInt_restrict : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      ((volume : Measure EuclN).restrict Set.univ) :=
    locallyIntegrable_to_restrict_univ (d := d) h_partial_locInt
  have h_inner_wp :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
        (fun y => (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y)
        (fun y => (η y)^2 * diffQuot k h u y) Set.univ :=
    hasWeakPartialDeriv_eta_sq_diffQuot (d := d) k j h hη
      hu_locInt hg_j_locInt hwp
  have h_eq :
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y) =
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y) := by
    funext y
    rw [fderiv_fun_pow 2 (hη_diff y)]
    rw [smul_apply]
    have h1 : (η y) ^ ((2 : ℕ) - 1) = η y := by norm_num
    rw [h1]
    have h_two : ((2 : ℕ) • η y) = 2 * η y := by
      rw [two_smul]; ring
    rw [h_two, smul_eq_mul]
  rw [h_eq] at h_inner_wp
  unfold standardNirenbergTest
  exact hasWeakPartialDeriv_diffQuot (d := d) k j (-h)
    h_F_locInt_restrict h_partial_locInt_restrict h_inner_wp

omit [NeZero d] in
private lemma eLpNorm_const_mul
    (c : ℝ) (f : EuclN → ℝ) :
    eLpNorm (fun x => c * f x) 2 (volume : Measure EuclN) =
      ENNReal.ofReal |c| * eLpNorm f 2 (volume : Measure EuclN) := by
  have h_eq : (fun x => c * f x) = c • f := by
    funext x; rw [Pi.smul_apply, smul_eq_mul]
  rw [h_eq]
  rw [eLpNorm_const_smul c f]
  simp [Real.enorm_eq_ofReal_abs]

omit [NeZero d] in
private lemma eLpNorm_translate_eq (k : Fin d) (h : ℝ) (F : EuclN → ℝ) :
    eLpNorm (translate k h F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : MeasurePreserving τ volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact measurePreserving_add_right volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq : translate k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show eLpNorm F 2 (volume : Measure EuclN) =
      eLpNorm F 2 (Measure.map τ volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

omit [NeZero d] in
private lemma eLpNorm_diffQuot_neg_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN)) :
    eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := by
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_eq : diffQuot k (-h) F =
      fun x => (-h)⁻¹ * (translate k (-h) F x - F x) := by
    funext x
    rw [diffQuot_apply_of_ne (d := d) k hnh F x]
    change (F (x + (-h) • EuclideanSpace.single k 1) - F x) / (-h) =
      (-h)⁻¹ * (F (x + (-h) • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq2 : (fun x => (-h)⁻¹ * (translate k (-h) F x - F x)) =
      fun x => (-h)⁻¹ * ((translate k (-h) F - F) x) := by
    funext x; simp [Pi.sub_apply]
  rw [h_eq2, eLpNorm_const_mul (-h)⁻¹ (translate k (-h) F - F)]
  have hτF_aesm : AEStronglyMeasurable (translate k (-h) F)
      (volume : Measure EuclN) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1)
        volume volume :=
      measurePreserving_add_right volume _
    exact hF_aesm.comp_measurePreserving hMP
  have h_minkowski : eLpNorm (translate k (-h) F - F) 2
      (volume : Measure EuclN) ≤
        eLpNorm (translate k (-h) F) 2 (volume : Measure EuclN) +
          eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_sub_le hτF_aesm hF_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_τF_eq : eLpNorm (translate k (-h) F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_translate_eq (d := d) k (-h) F
  rw [h_τF_eq] at h_minkowski
  have h_step : eLpNorm (translate k (-h) F - F) 2 (volume : Measure EuclN) ≤
      2 * eLpNorm F 2 (volume : Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |(-h)⁻¹| = |h|⁻¹ := by
    rw [abs_inv, abs_neg]
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |(-h)⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  rw [h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        eLpNorm (translate k (-h) F - F) 2 (volume : Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ * (2 * eLpNorm F 2 (volume : Measure EuclN)) := by
        gcongr
    _ = 2 / ENNReal.ofReal |h| * eLpNorm F 2 (volume : Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

omit [NeZero d] in
private lemma eLpNorm_eta_sq_diffQuot_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (_hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (fun y => (η y)^2 * diffQuot k h u y) 2
        (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  have h_pow_eq : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have h_pt : ∀ y : EuclN,
      (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) * (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
    intro y
    have h_real : ((η y)^2 * diffQuot k h u y)^2 ≤
        M_η^4 * (diffQuot k h u y)^2 := by
      have h_eta_sq_le : (η y)^2 ≤ M_η^2 := by
        have hY := hM_η y
        have h_abs_sq : (η y)^2 = |η y|^2 := by rw [sq_abs]
        rw [h_abs_sq]
        exact pow_le_pow_left₀ (abs_nonneg _) hY 2
      have h_eta_sq_sq_le : ((η y)^2)^2 ≤ (M_η^2)^2 := by
        have h_sq_nn : 0 ≤ (η y)^2 := sq_nonneg _
        exact pow_le_pow_left₀ h_sq_nn h_eta_sq_le 2
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u y)^2 := sq_nonneg _
      have h_step : ((η y)^2 * diffQuot k h u y)^2 =
          ((η y)^2)^2 * (diffQuot k h u y)^2 := by ring
      have hM4 : (M_η^2)^2 = M_η^4 := by ring
      calc ((η y)^2 * diffQuot k h u y)^2
          = ((η y)^2)^2 * (diffQuot k h u y)^2 := h_step
        _ ≤ (M_η^2)^2 * (diffQuot k h u y)^2 :=
            mul_le_mul_of_nonneg_right h_eta_sq_sq_le h_dq_sq_nn
        _ = M_η^4 * (diffQuot k h u y)^2 := by rw [hM4]
    have h_lhs_eq :
        (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal (((η y)^2 * diffQuot k h u y)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_rhs_eq :
        (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((diffQuot k h u y)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq, h_rhs_eq]
    have hM4_nn : 0 ≤ M_η^4 := by positivity
    rw [show ENNReal.ofReal (M_η^4) *
        ENNReal.ofReal ((diffQuot k h u y)^2) =
      ENNReal.ofReal (M_η^4 * (diffQuot k h u y)^2) from
      (ENNReal.ofReal_mul hM4_nn).symm]
    exact ENNReal.ofReal_le_ofReal h_real
  have h_lint_le :
      ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) := by
    calc ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
        ≤ ∫⁻ y : EuclN, ENNReal.ofReal (M_η^4) *
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          refine lintegral_mono_ae ?_
          filter_upwards with y using h_pt y
      _ = ENNReal.ofReal (M_η^4) *
            ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top]
  rw [h2_toReal]
  have h_lhs_pow_eq :
      (∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  have h_rhs_pow_eq :
      (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  rw [h_lhs_pow_eq, h_rhs_pow_eq]
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by norm_num : (0 : ℝ) ≤ 1/2)) ?_
  have h_pull :
      (ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)) ^ ((1 : ℝ) / 2) =
        (ENNReal.ofReal (M_η^4))^((1 : ℝ) / 2) *
          (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ))^((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_pull]
  have h_sqrt_M4 :
      (ENNReal.ofReal (M_η^4))^((1 : ℝ) / 2) = ENNReal.ofReal (M_η^2) := by
    have hM2_nn : 0 ≤ M_η^2 := sq_nonneg _
    have h_M4_to_pow :
        ENNReal.ofReal (M_η^4) = (ENNReal.ofReal (M_η^2))^(2 : ℕ) := by
      rw [show M_η^4 = (M_η^2)^(2 : ℕ) from by ring,
        ENNReal.ofReal_pow hM2_nn 2]
    rw [h_M4_to_pow]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (M_η^2)) 2,
      ← ENNReal.rpow_mul]
    have h_calc : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
    rw [h_calc, ENNReal.rpow_one]
  rw [h_sqrt_M4]

omit [NeZero d] in
theorem eLpNorm_standardNirenbergTest_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {η u : EuclN → ℝ}
    (hη_cont : Continuous η)
    (hu_aesm : AEStronglyMeasurable u (volume : Measure EuclN))
    {M_η : ℝ} (hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (standardNirenbergTest k h η u) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  set F : EuclN → ℝ := fun y => (η y)^2 * diffQuot k h u y with hF_def
  have hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN) := by
    rw [hF_def]
    have h1 : AEStronglyMeasurable (fun y : EuclN => (η y)^2)
        (volume : Measure EuclN) :=
      (hη_cont.pow 2).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (diffQuot k h u) (volume : Measure EuclN) :=
      aestronglyMeasurable_diffQuot (d := d) k h hu_aesm
    exact h1.mul h2
  have h_step_A : eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_diffQuot_neg_le (d := d) k hh hF_aesm
  have h_step_B : eLpNorm F 2 (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
    rw [hF_def]
    exact eLpNorm_eta_sq_diffQuot_le (d := d) k h hM_η_nn hM_η
  have h_lhs_unfold : standardNirenbergTest k h η u = diffQuot k (-h) F := rfl
  rw [h_lhs_unfold]
  calc eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN)
      ≤ (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := h_step_A
    _ ≤ (2 / ENNReal.ofReal |h|) *
          (ENNReal.ofReal (M_η^2) *
            eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN)) := by
          gcongr
    _ = (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
        rw [mul_assoc]

end Poincare.Analysis.Sobolev.NirenbergStandardTest
