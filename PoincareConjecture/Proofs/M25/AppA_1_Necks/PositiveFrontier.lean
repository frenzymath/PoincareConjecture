import PoincareConjecture.Proofs.M25.AppA_1_Necks.SharpDepth

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem mem_closure_final_tail_of_mem_positive_closure
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) {y : M}
    (hy : y ∈ closure (N.region 0 N.epsilon⁻¹))
    (hyout : y ∉ N.carrier) {a : ℝ} (ha : a < N.epsilon⁻¹) :
    y ∈ closure (N.region a N.epsilon⁻¹) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  by_cases ha0 : a ≤ 0
  · have hsub : N.region 0 N.epsilon⁻¹ ⊆ N.region a N.epsilon⁻¹ := by
      intro x hx
      exact ⟨hx.1, ha0.trans_lt hx.2.1, hx.2.2⟩
    exact closure_mono hsub hy
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let K := N.coordinate_map '' (univ ×ˢ Icc 0 a)
  have hK : IsCompact K := N.isCompact_coordinate_slab (neg_lt_zero.mpr hL) ha
  have hKsub : K ⊆ N.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, (neg_lt_zero.mpr hL).trans_le hz.2.1,
      hz.2.2.trans_lt ha⟩
  have hcover : N.region 0 N.epsilon⁻¹ ⊆ K ∪ N.region a N.epsilon⁻¹ := by
    intro x hx
    by_cases hxa : (N.coordinate_inverse x).2 ≤ a
    · exact Or.inl ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hxa⟩,
        N.coordinate_map_coordinate_inverse hx.1⟩
    · exact Or.inr ⟨hx.1, lt_of_not_ge hxa, hx.2.2⟩
  have hmem := closure_mono hcover hy
  rw [closure_union, hK.isClosed.closure_eq] at hmem
  exact hmem.resolve_left (fun hx => hyout (hKsub hx))

theorem edist_le_positive_frontier
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) {x y : M} (hx : x ∈ N.carrier)
    (hy : y ∈ closure (N.region 0 N.epsilon⁻¹))
    (hyout : y ∉ N.carrier) :
    g.edist x y ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) *
        (N.epsilon⁻¹ - (N.coordinate_inverse x).2 +
          Real.sqrt 2 * (Real.pi + 1))) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let a := (max 0 (N.coordinate_inverse x).2 + N.epsilon⁻¹) / 2
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hm : max 0 (N.coordinate_inverse x).2 < N.epsilon⁻¹ :=
    max_lt hL (N.coordinate_inverse_mem x hx).2.2
  have ha : a < N.epsilon⁻¹ := by dsimp only [a]; linarith
  have hxa : (N.coordinate_inverse x).2 < a := by
    dsimp only [a]
    linarith [le_max_right 0 (N.coordinate_inverse x).2]
  have htail := N.mem_closure_final_tail_of_mem_positive_closure hy hyout ha
  let R := ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) *
    (N.epsilon⁻¹ - (N.coordinate_inverse x).2 + Real.sqrt 2 * (Real.pi + 1)))
  have hbound : N.region a N.epsilon⁻¹ ⊆ {z | g.edist x z ≤ R} := by
    intro z hz
    have h := N.edist_le_axial_add hx hz.1
    have hdiff : 0 ≤ (N.coordinate_inverse z).2 - (N.coordinate_inverse x).2 :=
      sub_nonneg.mpr (hxa.trans hz.2.1).le
    rw [abs_of_nonneg hdiff] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (add_le_add (sub_le_sub_right hz.2.2.le _) le_rfl)
      (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
  have hclosed : IsClosed {z | g.edist x z ≤ R} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  exact closure_minimal hbound hclosed htail

theorem exists_positive_frontier_quarter_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
      N'.center ∈ closure (N.region 0 N.epsilon⁻¹) →
      N'.center ∉ N.carrier →
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier ∧
      ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
        g.edist N.center N'.center ∧
      g.edist N.center N'.center ≤
        ENNReal.ofReal ((1.01 : ℝ) * N.scale * N.epsilon⁻¹) := by
  obtain ⟨epsilonS, hS, hScap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let C := Real.sqrt 2 * (Real.pi + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hden : 0 < 1000 * (C + 1) := by positivity
  refine ⟨min epsilonS (1 / (1000 * (C + 1))),
    lt_min hS (div_pos zero_lt_one hden), (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hepsilon hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hepos : 0 < N.epsilon := N.epsilon_pos
  have hr : 0 < N.scale := N.scale_pos
  have hr' : 0 < N'.scale := N'.scale_pos
  have hNs : N.epsilon ≤ epsilonS := hN.trans (min_le_left _ _)
  have hN's : N'.epsilon ≤ epsilonS := by rw [hepsilon]; exact hNs
  have hcap : N.epsilon ≤ 1 / 200 := hNs.trans hScap
  have hsmall : N.epsilon ≤ 1 / (1000 * (C + 1)) := hN.trans (min_le_right _ _)
  have hCe : (C + 1) * N.epsilon ≤ 1 / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    nlinarith
  have hCee : C * N.epsilon ≤ 1 / 1000 := by nlinarith [N.epsilon_pos]
  have hCL : C ≤ L / 1000 := by
    calc
      C ≤ (1 / 1000) / N.epsilon := (le_div_iff₀ N.epsilon_pos).mpr hCee
      _ = L / 1000 := by dsimp only [L]; ring
  have hb : (99 : ℝ) / 100 ≤ Real.sqrt (1 - N.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + N.epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hc' := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  have hinter : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hy N'.carrier N'.carrier_open hc'.1
    exact ⟨z, hz.1, hz'⟩
  have hratio := (hscale N N' hNs hN's hinter).2
  have hratioLower : (99 : ℝ) / 100 < N'.scale / N.scale := by
    linarith [(abs_lt.mp hratio).1]
  have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ N'.scale :=
    ((lt_div_iff₀ N.scale_pos).mp hratioLower).le
  have hycarrier : N'.center ∈ closure N.carrier :=
    closure_mono (fun _ hx => hx.1) hy
  have hcenters := N.edist_center_closure_bounds hycarrier hyout
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_contra hxout
    have hupper := N.edist_le_positive_frontier hx.1 hy hyout
    have hupperReal : N.scale * Real.sqrt (1 + N.epsilon) *
        (L - (N.coordinate_inverse x).2 + C) ≤
        (50601 : ℝ) / 100000 * N.scale * L := by
      calc
        _ ≤ N.scale * Real.sqrt (1 + N.epsilon) * (L / 2 + C) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2.1])
            (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
        _ ≤ N.scale * (101 / 100) * (L / 2 + C) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp N.scale_pos.le) (by positivity)
        _ ≤ N.scale * (101 / 100) * (L / 2 + L / 1000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hCL)
            (by positivity)
        _ = _ := by ring
    have hu : g.edist x N'.center ≤
        ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) :=
      hupper.trans (ENNReal.ofReal_le_ofReal hupperReal)
    have hd : ENNReal.ofReal (N'.scale * Real.sqrt (1 - N.epsilon) * L) ≤
        g.edist x N'.center := by
      simpa only [axialDepth, if_neg hxout, if_pos hc'.1, hc'.2, abs_zero,
        sub_zero, zero_sub, abs_neg, hepsilon,
        abs_of_pos (inv_pos.mpr N.epsilon_pos)] using
        N'.axialDepth_edist_le x N'.center
    have hlowerReal : (9801 : ℝ) / 10000 * N.scale * L ≤
        N'.scale * Real.sqrt (1 - N.epsilon) * L := by
      calc
        _ = ((99 / 100) * N.scale) * (99 / 100) * L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul hscaleLower hb (by norm_num) N'.scale_pos.le) hL.le
    have hbad := ((ENNReal.ofReal_le_ofReal hlowerReal).trans hd).trans hu
    have hstrict : ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) <
        ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * L) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      nlinarith [mul_pos N.scale_pos hL]
    exact (not_le_of_gt hstrict) hbad
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hcenters.1
    calc
      (0.99 : ℝ) * N.scale * N.epsilon⁻¹ = N.scale * (99 / 100) * L := by
        dsimp only [L]
        ring
      _ ≤ N.scale * Real.sqrt (1 - N.epsilon) * L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb N.scale_pos.le) hL.le
  · apply hcenters.2.trans
    apply ENNReal.ofReal_le_ofReal
    have heone : N.epsilon ≤ 1 := hcap.trans (by norm_num)
    have hp' : Real.sqrt (1 + N.epsilon) ≤ 1 + N.epsilon :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [N.epsilon_pos]⟩
    have hesq : N.epsilon ^ 2 ≤ N.epsilon := by nlinarith [N.epsilon_pos]
    have hfactor : Real.sqrt (1 + N.epsilon) * (1 + C * N.epsilon) ≤
        (1.01 : ℝ) := by
      calc
        _ ≤ (1 + N.epsilon) * (1 + C * N.epsilon) :=
          mul_le_mul_of_nonneg_right hp' (by positivity)
        _ ≤ 1 + 2 * (C + 1) * N.epsilon := by
          nlinarith [mul_le_mul_of_nonneg_left hesq hC.le, N.epsilon_pos]
        _ ≤ _ := by nlinarith
    have hLe : L * N.epsilon = 1 := inv_mul_cancel₀ N.epsilon_pos.ne'
    have hsum : L + C = L * (1 + C * N.epsilon) := by
      calc
        L + C = L + C * (L * N.epsilon) := by rw [hLe]; ring
        _ = _ := by ring
    change N.scale * Real.sqrt (1 + N.epsilon) * (L + C) ≤
      (1.01 : ℝ) * N.scale * L
    calc
      _ = N.scale * L * (Real.sqrt (1 + N.epsilon) * (1 + C * N.epsilon)) := by
        rw [hsum]
        ring
      _ ≤ N.scale * L * (1.01 : ℝ) :=
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg N.scale_pos.le hL.le)
      _ = _ := by ring

end PoincareConjecture.EpsilonNeck
