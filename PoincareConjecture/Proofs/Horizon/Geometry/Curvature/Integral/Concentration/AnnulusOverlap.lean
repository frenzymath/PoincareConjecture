import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.GeometricAnnuli


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace Poincare.CurvatureIntegral



theorem card_geometric_annuli_mem_le
    {A B r₀ q : ℝ} {L : ℕ} (hB : 0 < B) (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q ≤ 1) (hgap : B * q ^ L < A)
    (F : Finset ℕ) (d : ℝ) :
    (F.filter (fun j => A * (r₀ * q ^ j) ≤ d ∧ d ≤ B * (r₀ * q ^ j))).card ≤ L := by
  classical
  let S := F.filter (fun j => A * (r₀ * q ^ j) ≤ d ∧ d ≤ B * (r₀ * q ^ j))
  change S.card ≤ L
  by_cases hS : S.Nonempty
  · let j₀ := S.min' hS
    have hj₀ : j₀ ∈ S := Finset.min'_mem S hS
    have hlow := (Finset.mem_filter.mp hj₀).2.1
    have hrj : 0 < r₀ * q ^ j₀ := mul_pos hr₀ (pow_pos hq _)
    have hsub : S ⊆ Finset.Ico j₀ (j₀ + L) := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨Finset.min'_le _ _ hj, ?_⟩
      by_contra hnot
      have hpow := pow_le_pow_of_le_one hq.le hq1 (le_of_not_gt hnot)
      have hjupper := (Finset.mem_filter.mp hj).2.2
      have hupper : B * (r₀ * q ^ j) < A * (r₀ * q ^ j₀) := by
        calc
          _ ≤ B * (r₀ * q ^ (j₀ + L)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hr₀.le) hB.le
          _ = (B * q ^ L) * (r₀ * q ^ j₀) := by rw [pow_add]; ring
          _ < _ := mul_lt_mul_of_pos_right hgap hrj
      exact (not_lt_of_ge hlow) (hjupper.trans_lt hupper)
    exact (Finset.card_le_card hsub).trans_eq (by simp)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le L



theorem sum_integral_geometric_annuli_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} (p : X) {W : Set X} {K : X → ℝ}
    (hW : MeasurableSet W) (hKi : IntegrableOn K W μ) (hKn : ∀ x, 0 ≤ K x)
    {A B r₀ q : ℝ} {L : ℕ} (hB : 0 < B) (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q ≤ 1) (hgap : B * q ^ L < A)
    (F : Finset ℕ)
    (hsub : ∀ j ∈ F,
      {x | A * (r₀ * q ^ j) ≤ dist p x ∧ dist p x ≤ B * (r₀ * q ^ j)} ⊆ W) :
    (∑ j ∈ F, ∫ x in {x | A * (r₀ * q ^ j) ≤ dist p x ∧
        dist p x ≤ B * (r₀ * q ^ j)}, K x ∂μ) ≤
      (L : ℝ) * ∫ x in W, K x ∂μ := by
  classical
  let U := fun j : ℕ => {x | A * (r₀ * q ^ j) ≤ dist p x ∧
    dist p x ≤ B * (r₀ * q ^ j)}
  have hUm (j : ℕ) : MeasurableSet (U j) :=
    ((isClosed_le continuous_const (continuous_const.dist continuous_id)).inter
      (isClosed_le (continuous_const.dist continuous_id) continuous_const)).measurableSet
  have hUi (j : ℕ) (hj : j ∈ F) : Integrable ((U j).indicator K) μ :=
    (integrable_indicator_iff (hUm j)).mpr (hKi.mono_set (hsub j hj))
  have hWi : Integrable (W.indicator K) μ :=
    (integrable_indicator_iff hW).mpr hKi
  have hpoint (x : X) : (∑ j ∈ F, (U j).indicator K x) ≤
      (L : ℝ) * W.indicator K x := by
    by_cases hx : x ∈ W
    · rw [indicator_of_mem hx]
      have he : (∑ j ∈ F, (U j).indicator K x) =
          ((F.filter (fun j => x ∈ U j)).card : ℝ) * K x := by
        simp only [Set.indicator, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
        congr 1
        congr 1
        congr 1
        ext j
        simp only [Finset.mem_filter]
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (card_geometric_annuli_mem_le hB hr₀ hq hq1 hgap F
          (dist p x))) (hKn x)
    · rw [indicator_of_notMem hx]
      have hz (j : ℕ) (hj : j ∈ F) : (U j).indicator K x = 0 :=
        indicator_of_notMem (fun hxj => hx (hsub j hj hxj)) K
      simp only [Finset.sum_congr rfl hz, Finset.sum_const_zero, mul_zero, le_refl]
  have hi := integral_mono (integrable_finsetSum F hUi) (hWi.const_mul (L : ℝ)) hpoint
  rw [integral_finsetSum F hUi, integral_const_mul, integral_indicator hW] at hi
  change (∑ j ∈ F, ∫ x in U j, K x ∂μ) ≤ _
  calc
    _ = ∑ j ∈ F, ∫ x, (U j).indicator K x ∂μ :=
      Finset.sum_congr rfl (fun j _ => (integral_indicator (hUm j)).symm)
    _ ≤ _ := hi



theorem exists_buffered_annulus_overlap :
    ∃ L : ℕ, 0 < L ∧ 3 * (227 / 228 : ℝ) ^ L < 1 / 2 := by
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 6 by norm_num)
    (show (227 / 228 : ℝ) < 1 by norm_num)
  refine ⟨L, ?_, ?_⟩
  · by_contra h
    have hzero : L = 0 := by omega
    norm_num [hzero] at hL
  · linarith




theorem integral_le_of_weighted_geometric_annulus_bounds
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {E : Set X} (hE : IsCompact E) (p : X)
    {W : Set X} {K : X → ℝ} (hW : MeasurableSet W)
    (hKi : IntegrableOn K W μ) (hKn : ∀ x, 0 ≤ K x)
    {A B A' B' r₀ q C D : ℝ} {m L : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hB' : 0 < B') (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q < 1) (hgap : A < B * q)
    (hoverlap : B' * q ^ L < A') (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : 1 ≤ m)
    {h : X → ℝ} (hhn : ∀ x, 0 ≤ h x) (hEi : IntegrableOn h E μ)
    (hsub : E ⊆ {x | 0 < dist p x ∧ dist p x < B * r₀})
    (hi : ∀ j : ℕ, IntegrableOn h
      {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)} μ)
    (herror : ∀ j : ℕ,
      {x | A' * (r₀ * q ^ j) ≤ dist p x ∧ dist p x ≤ B' * (r₀ * q ^ j)} ⊆ W)
    (hbound : ∀ j : ℕ,
      (∫ x in {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)},
        h x ∂μ) ≤ C * (r₀ * q ^ j) ^ m +
          D * ∫ x in {x | A' * (r₀ * q ^ j) ≤ dist p x ∧
            dist p x ≤ B' * (r₀ * q ^ j)}, K x ∂μ) :
    (∫ x in E, h x ∂μ) ≤ C * r₀ ^ m / (1 - q ^ m) +
      D * (L : ℝ) * ∫ x in W, K x ∂μ := by
  classical
  obtain ⟨F, hcover⟩ := exists_finite_geometric_annulus_cover
    hE p hA hB hr₀ hq hq1 hgap hsub
  let U := fun j : ℕ =>
    {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)}
  let V := fun j : ℕ =>
    {x | A' * (r₀ * q ^ j) ≤ dist p x ∧ dist p x ≤ B' * (r₀ * q ^ j)}
  have hUm (j : ℕ) : MeasurableSet (U j) :=
    ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const)).measurableSet
  have hcoverBound := integral_le_sum_of_finset_cover hE.isClosed.measurableSet F U
    (fun j _ => hUm j) hhn hEi (fun j _ => hi j) hcover
  have hpow : |q ^ m| < 1 := by
    rw [abs_of_nonneg (pow_nonneg hq.le _)]
    exact pow_lt_one₀ hq.le hq1 (by omega)
  have hsum := (summable_geometric_of_abs_lt_one hpow).sum_le_tsum F
    (fun j _ => pow_nonneg (pow_nonneg hq.le m) j)
  rw [tsum_geometric_of_abs_lt_one hpow] at hsum
  have hgeom : (∑ j ∈ F, C * (r₀ * q ^ j) ^ m) ≤ C * r₀ ^ m / (1 - q ^ m) := by
    calc
      _ = C * r₀ ^ m * ∑ j ∈ F, (q ^ m) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, ← pow_mul, Nat.mul_comm j m, pow_mul]
        ring
      _ ≤ C * r₀ ^ m * (1 - q ^ m)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (pow_nonneg hr₀.le _))
      _ = _ := by rw [div_eq_mul_inv]
  have herr := sum_integral_geometric_annuli_le p hW hKi hKn hB' hr₀ hq hq1.le
    hoverlap F (fun j _ => herror j)
  calc
    _ ≤ ∑ j ∈ F, ∫ x in U j, h x ∂μ := hcoverBound
    _ ≤ ∑ j ∈ F, (C * (r₀ * q ^ j) ^ m + D * ∫ x in V j, K x ∂μ) :=
      Finset.sum_le_sum (fun j _ => hbound j)
    _ = (∑ j ∈ F, C * (r₀ * q ^ j) ^ m) + D * ∑ j ∈ F, ∫ x in V j, K x ∂μ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ C * r₀ ^ m / (1 - q ^ m) + D * ((L : ℝ) * ∫ x in W, K x ∂μ) :=
      add_le_add hgeom (mul_le_mul_of_nonneg_left herr hD)
    _ = _ := by ring


theorem integral_le_of_weighted_geometric_annulus_bounds_above_scale
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {E : Set X} (hE : IsCompact E) (p : X)
    {W : Set X} {K : X → ℝ} (hW : MeasurableSet W)
    (hKi : IntegrableOn K W μ) (hKn : ∀ x, 0 ≤ K x)
    {A B A' B' r₀ q C D s : ℝ} {m L : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hB' : 0 < B') (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q < 1) (hgap : A < B * q)
    (hoverlap : B' * q ^ L < A') (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : 1 ≤ m)
    (hs : 0 ≤ s) {h : X → ℝ} (hhn : ∀ x, 0 ≤ h x)
    (hEi : IntegrableOn h E μ)
    (hsub : E ⊆ {x | B * s < dist p x ∧ dist p x < B * r₀})
    (hi : ∀ j : ℕ, IntegrableOn h
      {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)} μ)
    (herror : ∀ j : ℕ,
      {x | A' * (r₀ * q ^ j) ≤ dist p x ∧ dist p x ≤ B' * (r₀ * q ^ j)} ⊆ W)
    (hbound : ∀ j : ℕ, s ≤ r₀ * q ^ j →
      (∫ x in {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)},
        h x ∂μ) ≤ C * (r₀ * q ^ j) ^ m +
          D * ∫ x in {x | A' * (r₀ * q ^ j) ≤ dist p x ∧
            dist p x ≤ B' * (r₀ * q ^ j)}, K x ∂μ) :
    (∫ x in E, h x ∂μ) ≤ C * r₀ ^ m / (1 - q ^ m) +
      D * (L : ℝ) * ∫ x in W, K x ∂μ := by
  classical
  have hEm : MeasurableSet E := hE.isClosed.measurableSet
  have hIi : Integrable (E.indicator h) μ := (integrable_indicator_iff hEm).mpr hEi
  have hIhn (x : X) : 0 ≤ E.indicator h x := indicator_nonneg (fun y _ => hhn y) x
  have hUbound (j : ℕ) :
      (∫ x in {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)},
        E.indicator h x ∂μ) ≤ C * (r₀ * q ^ j) ^ m +
          D * ∫ x in {x | A' * (r₀ * q ^ j) ≤ dist p x ∧
            dist p x ≤ B' * (r₀ * q ^ j)}, K x ∂μ := by
    by_cases hj : s ≤ r₀ * q ^ j
    · apply (integral_mono hIi.integrableOn (hi j) ?_).trans (hbound j hj)
      intro x
      by_cases hx : x ∈ E
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        exact hhn x
    · have hzero : ∀ x ∈ {x | A * (r₀ * q ^ j) < dist p x ∧
          dist p x < B * (r₀ * q ^ j)}, E.indicator h x = 0 := by
        intro x hx
        apply indicator_of_notMem
        intro hxE
        have hlo := (hsub hxE).1
        have hhi := hx.2
        have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hj) hB
        linarith
      have hUm : MeasurableSet {x | A * (r₀ * q ^ j) < dist p x ∧
          dist p x < B * (r₀ * q ^ j)} :=
        ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
          (isOpen_lt (continuous_const.dist continuous_id) continuous_const)).measurableSet
      rw [setIntegral_congr_fun hUm hzero, integral_zero]
      exact add_nonneg
        (mul_nonneg hC (pow_nonneg (mul_nonneg hr₀.le (pow_nonneg hq.le _)) _))
        (mul_nonneg hD (integral_nonneg hKn))
  have hbnd := integral_le_of_weighted_geometric_annulus_bounds hE p hW hKi hKn
    hA hB hB' hr₀ hq hq1 hgap hoverlap hC hD hm hIhn hIi.integrableOn
    (fun x hx => ⟨(mul_nonneg hB.le hs).trans_lt (hsub hx).1, (hsub hx).2⟩)
    (fun _ => hIi.integrableOn) herror hUbound
  rw [setIntegral_indicator hEm] at hbnd
  simpa only [inter_self] using hbnd

end Poincare.CurvatureIntegral
