import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveFrontier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal












set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_oriented_positive_frontier_graph :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
      N'.center ∈ closure (N.region 0 N.epsilon⁻¹) →
      N'.center ∉ N.carrier →
      ∃ (R : EpsilonNeck g) (f : UnitTwoSphere → ℝ),
        (R = N' ∨ R = N'.reverse) ∧
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
        (∀ q, f q ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹) ∧
        (∀ q, -(3 * N.epsilon⁻¹ / 10) < f q ∧
          f q < -(N.epsilon⁻¹ / 5)) ∧
        range (fun q : UnitTwoSphere =>
          N.coordinate_map (q, 3 * N.epsilon⁻¹ / 4)) =
          range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) := by
  classical
  obtain ⟨epsilonF, hF, hFcap, hfront⟩ :=
    exists_positive_frontier_quarter_control.{u}
  obtain ⟨epsilonG, hG, _, hgraph⟩ := exists_contained_slice_graph.{u}
  obtain ⟨epsilonS, hS, _, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let C := Real.sqrt 2 * (Real.pi + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hden : 0 < 1000 * (C + 1) := by positivity
  refine ⟨min epsilonF (min epsilonG (min epsilonS (1 / (1000 * (C + 1))))),
    lt_min hF (lt_min hG (lt_min hS (div_pos zero_lt_one hden))),
    (min_le_left _ _).trans hFcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hepsilon hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hr : 0 < N.scale := N.scale_pos
  have hNF : N.epsilon ≤ epsilonF := hN.trans (min_le_left _ _)
  have hNG : N.epsilon ≤ epsilonG :=
    hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNS : N.epsilon ≤ epsilonS :=
    hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : N.epsilon ≤ 1 / (1000 * (C + 1)) :=
    hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcap : N.epsilon ≤ 1 / 200 := hNF.trans hFcap
  have hCL : C ≤ L / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    have hCe : C * N.epsilon ≤ 1 / 1000 := by nlinarith [N.epsilon_pos]
    calc
      C ≤ (1 / 1000) / N.epsilon := (le_div_iff₀ N.epsilon_pos).mpr hCe
      _ = L / 1000 := by dsimp only [L]; ring
  have hb : (99 : ℝ) / 100 ≤ Real.sqrt (1 - N.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + N.epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hc' := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  have hinter : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hy N'.carrier N'.carrier_open hc'.1
    exact ⟨z, hz.1, hz'⟩
  have hratio := (hscale N N' hNS (by rw [hepsilon]; exact hNS) hinter).2
  have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ N'.scale :=
    ((lt_div_iff₀ N.scale_pos).mp
      (show (99 : ℝ) / 100 < N'.scale / N.scale by
        linarith [(abs_lt.mp hratio).1])).le
  have hscaleUpper : N'.scale ≤ (101 : ℝ) / 100 * N.scale :=
    ((div_lt_iff₀ N.scale_pos).mp
      (show N'.scale / N.scale < (101 : ℝ) / 100 by
        linarith [(abs_lt.mp hratio).2])).le
  have hprodLower : (9801 : ℝ) / 10000 * N.scale ≤
      N'.scale * Real.sqrt (1 - N.epsilon) := by
    calc
      _ = ((99 / 100) * N.scale) * (99 / 100) := by ring
      _ ≤ _ := mul_le_mul hscaleLower hb (by norm_num) N'.scale_pos.le
  have hprodUpper : N'.scale * Real.sqrt (1 + N.epsilon) ≤
      (10201 : ℝ) / 10000 * N.scale := by
    calc
      _ ≤ ((101 / 100) * N.scale) * (101 / 100) :=
        mul_le_mul hscaleUpper hp (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  let t := 3 * L / 4
  have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    change -L < t ∧ t < L
    dsimp only [t]
    constructor <;> linarith
  have htpos : 0 < t := by dsimp only [t]; positivity
  have hquarter := (hfront N N' hNF hepsilon hy hyout).1
  have hslice : ∀ q : UnitTwoSphere, N.coordinate_map (q, t) ∈ N'.carrier := by
    intro q
    apply hquarter
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, ht⟩, ?_⟩
    rw [N.coordinate_inverse_map (q, t) ht]
    change L / 2 < t ∧ t < L
    dsimp only [t]
    constructor <;> linarith
  obtain ⟨⟨h, hh, hdom, heq⟩, _⟩ :=
    hgraph N' N (by rw [hepsilon]; exact hNG) hNG t ht hslice
  have habs : ∀ q, L / 5 < |h q| ∧ |h q| < 3 * L / 10 := by
    intro q
    let w := N'.coordinate_map (q, h q)
    have hwRange : w ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, t)) := by
      rw [← heq]
      exact mem_range_self q
    obtain ⟨p, hpw⟩ := hwRange
    have hwN : w ∈ N.carrier := hpw ▸ N.coordinate_map_mem ⟨mem_univ _, ht⟩
    have hwN' : w ∈ N'.carrier := N'.coordinate_map_mem ⟨mem_univ _, hdom q⟩
    have hwheight : (N.coordinate_inverse w).2 = t := by
      rw [← hpw, N.coordinate_inverse_map (p, t) ht]
    have hwh : (N'.coordinate_inverse w).2 = h q := by
      exact congrArg Prod.snd (N'.coordinate_inverse_map (q, h q) (hdom q))
    have hwdepth : N.axialDepth w = L / 4 := by
      rw [axialDepth, if_pos hwN, hwheight, abs_of_pos htpos]
      dsimp only [t, L]
      ring
    have hydepth : N.axialDepth N'.center = 0 := by simp only [axialDepth, if_neg hyout]
    have holdLower : ENNReal.ofReal ((2475 : ℝ) / 10000 * N.scale * L) ≤
        g.edist w N'.center := by
      have hd := N.axialDepth_edist_le w N'.center
      rw [hwdepth, hydepth, sub_zero, abs_of_pos (by positivity : 0 < L / 4)] at hd
      apply (ENNReal.ofReal_le_ofReal ?_).trans hd
      calc
        _ = N.scale * (99 / 100) * (L / 4) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb N.scale_pos.le) (by positivity)
    have holdUpper : g.edist w N'.center ≤
        ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) := by
      have hu := N.edist_le_positive_frontier hwN hy hyout
      rw [hwheight] at hu
      apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
      change N.scale * Real.sqrt (1 + N.epsilon) * (L - t + C) ≤ _
      calc
        _ = N.scale * Real.sqrt (1 + N.epsilon) * (L / 4 + C) := by
          dsimp only [t]
          ring
        _ ≤ N.scale * (101 / 100) * (L / 4 + C) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp N.scale_pos.le)
            (by positivity)
        _ ≤ N.scale * (101 / 100) * (L / 4 + L / 1000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hCL) (by positivity)
        _ = _ := by ring
    have hnewLower : ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * |h q|) ≤
        g.edist w N'.center := by
      have hdiff : N'.axialDepth w - N'.axialDepth N'.center = -|h q| := by
        simp only [axialDepth, if_pos hwN', if_pos hc'.1, hwh, hc'.2, abs_zero, sub_zero]
        ring
      have hd := N'.axialDepth_edist_le w N'.center
      rw [hdiff, abs_neg, abs_abs, hepsilon] at hd
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hprodLower (abs_nonneg _))).trans hd
    have hnewUpper : g.edist w N'.center ≤
        ENNReal.ofReal ((10201 : ℝ) / 10000 * N.scale * (|h q| + C)) := by
      have hu := N'.edist_le_axial_add hwN' hc'.1
      rw [hc'.2, hwh, zero_sub, abs_neg, hepsilon] at hu
      exact hu.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hprodUpper (add_nonneg (abs_nonneg _) hC.le)))
    constructor
    · by_contra hn
      have ha : |h q| ≤ L / 5 := le_of_not_gt hn
      have hu : g.edist w N'.center ≤
          ENNReal.ofReal ((2050401 : ℝ) / 10000000 * N.scale * L) := by
        apply hnewUpper.trans (ENNReal.ofReal_le_ofReal ?_)
        calc
          _ ≤ (10201 : ℝ) / 10000 * N.scale * (L / 5 + L / 1000) :=
            mul_le_mul_of_nonneg_left (add_le_add ha hCL) (by positivity)
          _ = _ := by ring
      have hstrict : ENNReal.ofReal ((2050401 : ℝ) / 10000000 * N.scale * L) <
          ENNReal.ofReal ((2475 : ℝ) / 10000 * N.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith [mul_pos N.scale_pos hL]
      exact (not_le_of_gt hstrict) (holdLower.trans hu)
    · by_contra hn
      have ha : 3 * L / 10 ≤ |h q| := le_of_not_gt hn
      have hd : ENNReal.ofReal ((29403 : ℝ) / 100000 * N.scale * L) ≤
          g.edist w N'.center := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans hnewLower
        calc
          _ = (9801 : ℝ) / 10000 * N.scale * (3 * L / 10) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)
      have hstrict : ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) <
          ENNReal.ofReal ((29403 : ℝ) / 100000 * N.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith [mul_pos N.scale_pos hL]
      exact (not_le_of_gt hstrict) (hd.trans holdUpper)
  have hnonzero : ∀ q ∈ (univ : Set UnitTwoSphere), h q ≠ 0 := by
    intro q _ hq
    have hbq := (habs q).1
    rw [hq, abs_zero] at hbq
    linarith
  rcases isPreconnected_univ.mapsTo_Ioi_or_Iio hh.continuous.continuousOn hnonzero with
    hpositive | hnegative
  · refine ⟨N'.reverse, fun q => -h q, Or.inr rfl,
      contDiff_neg.contMDiff.comp hh, ?_, ?_, ?_⟩
    · intro q
      change -N'.epsilon⁻¹ < -h q ∧ -h q < N'.epsilon⁻¹
      constructor <;> linarith [(hdom q).1, (hdom q).2]
    · intro q
      have hq : 0 < h q := hpositive (mem_univ q)
      have hbq := habs q
      rw [abs_of_pos hq] at hbq
      change -(3 * L / 10) < -h q ∧ -h q < -(L / 5)
      constructor <;> linarith [hbq.1, hbq.2]
    · change range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) =
        range (fun q : UnitTwoSphere => N'.coordinate_map (q, - -h q))
      simpa only [neg_neg] using heq.symm
  · refine ⟨N', h, Or.inl rfl, hh, hdom, ?_, heq.symm⟩
    intro q
    have hq : h q < 0 := hnegative (mem_univ q)
    have hbq := habs q
    rw [abs_of_neg hq] at hbq
    change -(3 * L / 10) < h q ∧ h q < -(L / 5)
    constructor <;> linarith [hbq.1, hbq.2]

end PoincareConjecture.EpsilonNeck
