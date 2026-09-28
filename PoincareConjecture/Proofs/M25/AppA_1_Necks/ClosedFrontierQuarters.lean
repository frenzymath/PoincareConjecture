import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveFrontier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_positive_frontier_closed_quarter_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
      N'.center ∈ closure (N.region 0 N.epsilon⁻¹) →
      N'.center ∉ N.carrier →
      closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆ N'.carrier := by
  obtain ⟨epsilonS, hS, hScap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let B := Real.sqrt 2 * (Real.pi + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hden : 0 < 1000 * (B + 1) := by positivity
  refine ⟨min epsilonS (1 / (1000 * (B + 1))),
    lt_min hS (div_pos zero_lt_one hden), (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hepsilon hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hr : 0 < N.scale := N.scale_pos
  have hNs : N.epsilon ≤ epsilonS := hN.trans (min_le_left _ _)
  have hcap : N.epsilon ≤ 1 / 200 := hNs.trans hScap
  have hsmall : N.epsilon ≤ 1 / (1000 * (B + 1)) := hN.trans (min_le_right _ _)
  have hBL : B ≤ L / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    have hBe : B * N.epsilon ≤ 1 / 1000 := by nlinarith [N.epsilon_pos]
    calc
      B ≤ (1 / 1000) / N.epsilon := (le_div_iff₀ N.epsilon_pos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring
  have hb : (99 : ℝ) / 100 ≤ Real.sqrt (1 - N.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + N.epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hc := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  have hinter : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hy N'.carrier N'.carrier_open hc.1
    exact ⟨z, hz.1, hz'⟩
  have hratio := (hscale N N' hNs (by rw [hepsilon]; exact hNs) hinter).2
  have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ N'.scale :=
    ((lt_div_iff₀ N.scale_pos).mp
      (show (99 : ℝ) / 100 < N'.scale / N.scale by
        linarith [(abs_lt.mp hratio).1])).le
  have hbound : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      {z | g.edist z N'.center ≤
        ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L)} := by
    intro z hz
    have hu := N.edist_le_positive_frontier hz.1 hy hyout
    apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
    change N.scale * Real.sqrt (1 + N.epsilon) *
      (L - (N.coordinate_inverse z).2 + B) ≤ _
    calc
      _ ≤ N.scale * Real.sqrt (1 + N.epsilon) * (L / 2 + B) :=
        mul_le_mul_of_nonneg_left (by linarith [hz.2.1])
          (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
      _ ≤ N.scale * (101 / 100) * (L / 2 + B) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp N.scale_pos.le) (by positivity)
      _ ≤ N.scale * (101 / 100) * (L / 2 + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hBL) (by positivity)
      _ = _ := by ring
  have hclosed : IsClosed {z | g.edist z N'.center ≤
      ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L)} :=
    isClosed_le (continuous_id.edist continuous_const) continuous_const
  intro x hx
  have hu := closure_minimal hbound hclosed hx
  by_contra hxout
  have hd : ENNReal.ofReal (N'.scale * Real.sqrt (1 - N.epsilon) * L) ≤
      g.edist x N'.center := by
    simpa only [axialDepth, if_neg hxout, if_pos hc.1, hc.2, abs_zero,
      sub_zero, zero_sub, abs_neg, hepsilon,
      abs_of_pos (inv_pos.mpr N.epsilon_pos)] using
      N'.axialDepth_edist_le x N'.center
  have hlower : (9801 : ℝ) / 10000 * N.scale * L ≤
      N'.scale * Real.sqrt (1 - N.epsilon) * L := by
    calc
      _ = ((99 / 100) * N.scale) * (99 / 100) * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hscaleLower hb (by norm_num) N'.scale_pos.le) hL.le
  have hstrict : ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) <
      ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * L) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_pos N.scale_pos hL]
  exact (not_le_of_gt hstrict) (((ENNReal.ofReal_le_ofReal hlower).trans hd).trans hu)




theorem exists_positive_frontier_closed_negative_quarter_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N R : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → R.epsilon = N.epsilon →
      N.IsSeparating →
      R.center ∈ closure (N.region 0 N.epsilon⁻¹) →
      R.center ∉ N.carrier →
      R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆ N.carrier →
      closure (R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) ⊆ N.carrier := by
  obtain ⟨epsilonS, hS, hScap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let B := Real.sqrt 2 * (Real.pi + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hden : 0 < 1000 * (B + 1) := by positivity
  refine ⟨min epsilonS (1 / (1000 * (B + 1))),
    lt_min hS (div_pos zero_lt_one hden), (min_le_left _ _).trans hScap, ?_⟩
  intro M _ _ _ _ _ _ g N R hN hepsilon hsep hy hyout hquarter
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hr : 0 < N.scale := N.scale_pos
  have hNs : N.epsilon ≤ epsilonS := hN.trans (min_le_left _ _)
  have hcap : N.epsilon ≤ 1 / 200 := hNs.trans hScap
  have hsmall : N.epsilon ≤ 1 / (1000 * (B + 1)) := hN.trans (min_le_right _ _)
  have hBL : B ≤ L / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    have hBe : B * N.epsilon ≤ 1 / 1000 := by nlinarith [N.epsilon_pos]
    calc
      B ≤ (1 / 1000) / N.epsilon := (le_div_iff₀ N.epsilon_pos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring
  have hb : (99 : ℝ) / 100 ≤ Real.sqrt (1 - N.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + N.epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hc := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
  have hinter : (N.carrier ∩ R.carrier).Nonempty := by
    obtain ⟨z, hzR, hz⟩ := mem_closure_iff.mp hy R.carrier R.carrier_open hc.1
    exact ⟨z, hz.1, hzR⟩
  have hratio := (hscale N R hNs (by rw [hepsilon]; exact hNs) hinter).2
  have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ R.scale :=
    ((lt_div_iff₀ N.scale_pos).mp
      (show (99 : ℝ) / 100 < R.scale / N.scale by
        linarith [(abs_lt.mp hratio).1])).le
  have hscaleUpper : R.scale ≤ (101 : ℝ) / 100 * N.scale :=
    ((div_lt_iff₀ N.scale_pos).mp
      (show R.scale / N.scale < (101 : ℝ) / 100 by
        linarith [(abs_lt.mp hratio).2])).le
  have hprodLower : (9801 : ℝ) / 10000 * N.scale ≤
      R.scale * Real.sqrt (1 - N.epsilon) := by
    calc
      _ = ((99 / 100) * N.scale) * (99 / 100) := by ring
      _ ≤ _ := mul_le_mul hscaleLower hb (by norm_num) R.scale_pos.le
  have hprodUpper : R.scale * Real.sqrt (1 + N.epsilon) ≤
      (10201 : ℝ) / 10000 * N.scale := by
    calc
      _ ≤ ((101 / 100) * N.scale) * (101 / 100) :=
        mul_le_mul hscaleUpper hp (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨a, b, ha, hbside, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components hsep
  obtain ⟨H, hH, hinside, hminus, hplus, _, hdist⟩ :=
    N.exists_saturatedAxialHeight hsep a b ha hbside
  have hout {x : M} (hxK : x ∈ connectedComponent N.center) (hx : x ∉ N.carrier) :
      H x = -L ∨ H x = L := by
    rw [← hcover] at hxK
    rcases hxK with (hxA | hxS) | hxB
    · exact Or.inl (hminus x ⟨hxA, hx⟩)
    · exact False.elim (hx (N.central_sphere_subset hxS))
    · exact Or.inr (hplus x ⟨hxB, hx⟩)
  have hyK : R.center ∈ connectedComponent N.center :=
    closure_minimal (fun _ hx => N.m25_carrier_subset_connectedComponent hx.1)
      isClosed_connectedComponent hy
  have hyH : H R.center = L := by
    have hypos : 0 ≤ H R.center := by
      apply closure_minimal (t := {x | 0 ≤ H x}) ?_
        (isClosed_le continuous_const hH) hy
      intro z hz
      change 0 ≤ H z
      rw [hinside z hz.1]
      exact hz.2.1.le
    rcases hout hyK hyout with h | h
    · linarith
    · exact h
  have hRK : R.carrier ⊆ connectedComponent N.center := by
    intro z hz
    have hm := R.m25_carrier_subset_connectedComponent hz
    rw [← connectedComponent_eq hyK] at hm
    exact hm
  have hupper {z : M} (hz : z ∈ R.carrier) :
      g.edist z R.center ≤
        ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) := by
    have hu := R.edist_le_axial_add hz hc.1
    rw [hc.2, zero_sub, abs_neg, hepsilon] at hu
    have hheight : |(R.coordinate_inverse z).2| ≤ L := by
      simpa only [hepsilon] using (abs_lt.mpr (R.coordinate_inverse_mem z hz).2).le
    apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
    change R.scale * Real.sqrt (1 + N.epsilon) *
      (|(R.coordinate_inverse z).2| + B) ≤ _
    calc
      _ ≤ ((10201 : ℝ) / 10000 * N.scale) * (|(R.coordinate_inverse z).2| + B) :=
        mul_le_mul_of_nonneg_right hprodUpper (add_nonneg (abs_nonneg _) hB.le)
      _ ≤ ((10201 : ℝ) / 10000 * N.scale) * (L + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add hheight hBL) (by positivity)
      _ = _ := by ring
  have hnewLower {z : M} (hz : z ∈ R.carrier) :
      ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * |(R.coordinate_inverse z).2|) ≤
        g.edist z R.center := by
    have hdiff : R.axialDepth z - R.axialDepth R.center =
        -|(R.coordinate_inverse z).2| := by
      simp only [axialDepth, if_pos hz, if_pos hc.1, hc.2, abs_zero, sub_zero]
      ring
    have hd := R.axialDepth_edist_le z R.center
    rw [hdiff, abs_neg, abs_abs, hepsilon] at hd
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprodLower (abs_nonneg _))).trans hd
  have hheight : ∀ z ∈ R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2), H z < 3 * L / 4 := by
    intro z hz
    have hzN := hquarter hz
    rw [hinside z hzN]
    by_contra hn
    have hhigh : 3 * L / 4 ≤ (N.coordinate_inverse z).2 := le_of_not_gt hn
    have hu : g.edist z R.center ≤
        ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) := by
      have hu := N.edist_le_positive_frontier hzN hy hyout
      apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
      change N.scale * Real.sqrt (1 + N.epsilon) *
        (L - (N.coordinate_inverse z).2 + B) ≤ _
      calc
        _ ≤ N.scale * Real.sqrt (1 + N.epsilon) * (L / 4 + B) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
        _ ≤ N.scale * (101 / 100) * (L / 4 + B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp N.scale_pos.le)
            (by positivity)
        _ ≤ N.scale * (101 / 100) * (L / 4 + L / 1000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hBL) (by positivity)
        _ = _ := by ring
    have hgap : L / 2 ≤ |(R.coordinate_inverse z).2| := by
      have hzneg : (R.coordinate_inverse z).2 < -L / 2 := hz.2.2
      rw [abs_of_neg (by linarith : (R.coordinate_inverse z).2 < 0)]
      linarith
    have hd : ENNReal.ofReal ((49005 : ℝ) / 100000 * N.scale * L) ≤
        g.edist z R.center := by
      apply (ENNReal.ofReal_le_ofReal ?_).trans (hnewLower hz.1)
      calc
        _ = ((9801 : ℝ) / 10000 * N.scale) * (L / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
    have hstrict : ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) <
        ENNReal.ofReal ((49005 : ℝ) / 100000 * N.scale * L) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      nlinarith [mul_pos N.scale_pos hL]
    exact (not_le_of_gt hstrict) (hd.trans hu)
  have hheightClosure : closure (R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) ⊆
      {x | H x ≤ 3 * L / 4} :=
    closure_minimal (fun z hz => (hheight z hz).le) (isClosed_le hH continuous_const)
  have hupperClosure : closure (R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) ⊆
      {x | g.edist x R.center ≤
        ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L)} :=
    closure_minimal (fun _ hx => hupper hx.1)
      (isClosed_le (continuous_id.edist continuous_const) continuous_const)
  intro x hx
  by_contra hxout
  have hxK : x ∈ connectedComponent N.center :=
    closure_minimal (fun _ hz => hRK hz.1) isClosed_connectedComponent hx
  have hxH : H x = -L := by
    rcases hout hxK hxout with h | h
    · exact h
    · have hbnd := hheightClosure hx
      change H x ≤ 3 * L / 4 at hbnd
      linarith
  have hd : ENNReal.ofReal ((198 : ℝ) / 100 * N.scale * L) ≤
      g.edist x R.center := by
    have hd := hdist x R.center
    rw [hxH, hyH, show -L - L = -(2 * L) by ring, abs_neg,
      abs_of_pos (by positivity : 0 < 2 * L)] at hd
    apply (ENNReal.ofReal_le_ofReal ?_).trans hd
    calc
      _ = N.scale * (99 / 100) * (2 * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb N.scale_pos.le) (by positivity)
  have hstrict : ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) <
      ENNReal.ofReal ((198 : ℝ) / 100 * N.scale * L) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_pos N.scale_pos hL]
  exact (not_le_of_gt hstrict) (hd.trans (hupperClosure hx))

end PoincareConjecture.EpsilonNeck
