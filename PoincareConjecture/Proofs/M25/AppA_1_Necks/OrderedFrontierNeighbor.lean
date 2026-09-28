import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrientedFrontierGraph
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphSides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_ordered_frontier_neighbor :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
      N.IsSeparating →
      N'.center ∈ closure (N.region 0 N.epsilon⁻¹) →
      N'.center ∉ N.carrier →
      ∃ R : EpsilonNeck g,
        (R = N' ∨ R = N'.reverse) ∧
        R.SameUpToReversal N' ∧
        N.center ≠ R.center ∧
        (N.carrier ∩ R.carrier).Nonempty ∧
        (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ R.carrier ∧
          R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆ N.carrier) ∧
        (N.carrier ∩ R.carrier ⊆
          N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
            R.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2)) ∧
        (∃ s ∈ Ioo (-N.epsilon⁻¹) 0,
          Disjoint R.carrier (N.region (-N.epsilon⁻¹) s)) ∧
        (ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
            g.edist N.center R.center ∧
          g.edist N.center R.center ≤
            ENNReal.ofReal ((1.01 : ℝ) * N.scale * N.epsilon⁻¹)) := by
  classical
  obtain ⟨epsilonP, hP, hPcap, horient⟩ := exists_oriented_positive_frontier_graph.{u}
  obtain ⟨epsilonF, hF, _, hfront⟩ := exists_positive_frontier_quarter_control.{u}
  obtain ⟨epsilonS, hS, _, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let C := Real.sqrt 2 * (Real.pi + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hden : 0 < 1000 * (C + 1) := by positivity
  refine ⟨min epsilonP (min epsilonF (min epsilonS (1 / (1000 * (C + 1))))),
    lt_min hP (lt_min hF (lt_min hS (div_pos zero_lt_one hden))),
    (min_le_left _ _).trans hPcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hepsilon hsep hy hyout
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hr : 0 < N.scale := N.scale_pos
  have hNP : N.epsilon ≤ epsilonP := hN.trans (min_le_left _ _)
  have hNF : N.epsilon ≤ epsilonF :=
    hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNS : N.epsilon ≤ epsilonS :=
    hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : N.epsilon ≤ 1 / (1000 * (C + 1)) :=
    hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcap : N.epsilon ≤ 1 / 200 := hNP.trans hPcap
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
  obtain ⟨R, f, hchoice, hf, hdom, hquant, hgraph⟩ :=
    horient N N' hNP hepsilon hy hyout
  have heR : R.epsilon = N.epsilon := by
    rcases hchoice with rfl | rfl <;> exact hepsilon
  have hrR : R.scale = N'.scale := by rcases hchoice with rfl | rfl <;> rfl
  have hcR : R.center = N'.center := by rcases hchoice with rfl | rfl <;> rfl
  have huR : R.carrier = N'.carrier := by rcases hchoice with rfl | rfl <;> rfl
  have hselected : R.SameUpToReversal N' := by
    rcases hchoice with rfl | rfl
    · refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp
    · refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
      intro z _
      change N'.coordinate_map (z.1, -z.2) = N'.coordinate_map (z.1, -1 * z.2)
      simp
  have hc' := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  have hc := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
  have hinter : (N.carrier ∩ N'.carrier).Nonempty := by
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hy N'.carrier N'.carrier_open hc'.1
    exact ⟨z, hz.1, hz'⟩
  have hratio := (hscale N N' hNS (by rw [hepsilon]; exact hNS) hinter).2
  have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ R.scale := by
    rw [hrR]
    exact ((lt_div_iff₀ N.scale_pos).mp
      (show (99 : ℝ) / 100 < N'.scale / N.scale by
        linarith [(abs_lt.mp hratio).1])).le
  have hscaleUpper : R.scale ≤ (101 : ℝ) / 100 * N.scale := by
    rw [hrR]
    exact ((div_lt_iff₀ N.scale_pos).mp
      (show N'.scale / N.scale < (101 : ℝ) / 100 by
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
  have hyK : N'.center ∈ connectedComponent N.center :=
    closure_minimal (fun _ hx => N.m25_carrier_subset_connectedComponent hx.1)
      isClosed_connectedComponent hy
  have hyH : H N'.center = L := by
    have hnonnegative : N.region 0 N.epsilon⁻¹ ⊆ {x | 0 ≤ H x} := by
      intro x hx
      change 0 ≤ H x
      rw [hinside x hx.1]
      exact hx.2.1.le
    have hypos : 0 ≤ H N'.center :=
      closure_minimal hnonnegative (isClosed_le continuous_const hH) hy
    rcases hout hyK hyout with h | h
    · linarith
    · exact h
  have hRcenter : H R.center = L := by rw [hcR]; exact hyH
  have hRK : R.carrier ⊆ connectedComponent N.center := by
    intro x hx
    have hm := R.m25_carrier_subset_connectedComponent hx
    rw [hcR, ← connectedComponent_eq hyK] at hm
    exact hm
  let t := 3 * L / 4
  have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    change -L < t ∧ t < L
    dsimp only [t]
    constructor <;> linarith
  have hlevel : ∀ x ∈ R.carrier,
      H x = t ↔ x ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) := by
    intro x hxR
    by_cases hx : x ∈ N.carrier
    · rw [hinside x hx]
      constructor
      · intro hs
        refine ⟨(N.coordinate_inverse x).1, ?_⟩
        rw [← hs]
        exact N.coordinate_map_inverse hx
      · rintro ⟨q, rfl⟩
        rw [N.coordinate_inverse_map (q, t) ht]
    · have hne : H x ≠ t := by
        rcases hout (hRK hxR) hx with h | h <;> dsimp only [t] <;> linarith
      refine iff_of_false hne ?_
      rintro ⟨q, hq⟩
      exact hx (hq ▸ N.coordinate_map_mem ⟨mem_univ _, ht⟩)
  have hnegative : ∀ q, f q < 0 := by
    intro q
    have hq := (hquant q).2
    change f q < -(L / 5) at hq
    linarith
  have hsides := N.graph_sides_of_axial_level R H hH hinside ht hlevel f hf.continuous
    hdom hnegative hgraph (by rw [hRcenter]; dsimp only [t]; linarith)
  have hsigned (x : M) : ENNReal.ofReal
      ((99 : ℝ) / 100 * N.scale * |H x - L|) ≤ g.edist x R.center := by
    have hd := hdist x R.center
    rw [hRcenter] at hd
    apply (ENNReal.ofReal_le_ofReal ?_).trans hd
    calc
      _ = N.scale * (99 / 100) * |H x - L| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb N.scale_pos.le) (abs_nonneg _)
  have hupper {x : M} (hx : x ∈ R.carrier) :
      g.edist x R.center ≤
        ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) := by
    have hu := R.edist_le_axial_add hx hc.1
    rw [hc.2, zero_sub, abs_neg, heR] at hu
    have hheight : |(R.coordinate_inverse x).2| ≤ L := by
      have hm := (abs_lt.mpr (R.coordinate_inverse_mem x hx).2).le
      simpa only [heR] using hm
    apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
    change R.scale * Real.sqrt (1 + N.epsilon) *
      (|(R.coordinate_inverse x).2| + C) ≤ _
    calc
      _ ≤ ((10201 : ℝ) / 10000 * N.scale) * (|(R.coordinate_inverse x).2| + C) :=
        mul_le_mul_of_nonneg_right hprodUpper (add_nonneg (abs_nonneg _) hC.le)
      _ ≤ ((10201 : ℝ) / 10000 * N.scale) * (L + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add hheight hCL) (by positivity)
      _ = _ := by ring
  have hnewLower {x : M} (hx : x ∈ R.carrier) :
      ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * |(R.coordinate_inverse x).2|) ≤
        g.edist x R.center := by
    have hdiff : R.axialDepth x - R.axialDepth R.center =
        -|(R.coordinate_inverse x).2| := by
      simp only [axialDepth, if_pos hx, if_pos hc.1, hc.2, abs_zero, sub_zero]
      ring
    have hd := R.axialDepth_edist_le x R.center
    rw [hdiff, abs_neg, abs_abs, heR] at hd
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hprodLower (abs_nonneg _))).trans hd
  have hfrontUpper {x : M} (hx : x ∈ N.carrier)
      (hhigh : 3 * L / 4 < (N.coordinate_inverse x).2) :
      g.edist x R.center ≤ ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) := by
    rw [hcR]
    have hu := N.edist_le_positive_frontier hx hy hyout
    apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
    change N.scale * Real.sqrt (1 + N.epsilon) *
      (L - (N.coordinate_inverse x).2 + C) ≤ _
    calc
      _ ≤ N.scale * Real.sqrt (1 + N.epsilon) * (L / 4 + C) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
      _ ≤ N.scale * (101 / 100) * (L / 4 + C) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp N.scale_pos.le)
          (by positivity)
      _ ≤ N.scale * (101 / 100) * (L / 4 + L / 1000) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hCL) (by positivity)
      _ = _ := by ring
  have hnewQuarter : R.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆ N.carrier := by
    intro x hx
    by_contra hxout
    have hbelow : (R.coordinate_inverse x).2 < f (R.coordinate_inverse x).1 := by
      have hfq := (hquant (R.coordinate_inverse x).1).1
      change -(3 * L / 10) < f (R.coordinate_inverse x).1 at hfq
      have hxh : (R.coordinate_inverse x).2 < -L / 2 := hx.2.2
      linarith
    have hside := (hsides x hx.1).1.mpr hbelow
    have hxH : H x = -L := by
      rcases hout (hRK hx.1) hxout with h | h
      · exact h
      · dsimp only [t] at hside
        linarith
    have hd : ENNReal.ofReal ((198 : ℝ) / 100 * N.scale * L) ≤
        g.edist x R.center := by
      have hs := hsigned x
      rw [hxH, show -L - L = -(2 * L) by ring, abs_neg,
        abs_of_pos (by positivity : 0 < 2 * L)] at hs
      convert hs using 1
      congr 1
      ring
    have hstrict : ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) <
        ENNReal.ofReal ((198 : ℝ) / 100 * N.scale * L) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      nlinarith [mul_pos hr hL]
    exact (not_le_of_gt hstrict) (hd.trans (hupper hx.1))
  have hoverlap : N.carrier ∩ R.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        R.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) := by
    intro x hx
    have hOld : -L / 2 < (N.coordinate_inverse x).2 := by
      by_contra hn
      have hheight : H x ≤ -L / 2 := by rw [hinside x hx.1]; exact le_of_not_gt hn
      have hgap : 3 * L / 2 ≤ |H x - L| := by
        rw [abs_of_neg (by linarith : H x - L < 0)]
        linarith
      have hd : ENNReal.ofReal ((1485 : ℝ) / 1000 * N.scale * L) ≤
          g.edist x R.center := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans (hsigned x)
        calc
          _ = ((99 : ℝ) / 100 * N.scale) * (3 * L / 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
      have hstrict : ENNReal.ofReal ((10211201 : ℝ) / 10000000 * N.scale * L) <
          ENNReal.ofReal ((1485 : ℝ) / 1000 * N.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith [mul_pos hr hL]
      exact (not_le_of_gt hstrict) (hd.trans (hupper hx.2))
    have hNew : (R.coordinate_inverse x).2 < L / 2 := by
      by_contra hn
      have hheight : L / 2 ≤ (R.coordinate_inverse x).2 := le_of_not_gt hn
      have habove : f (R.coordinate_inverse x).1 < (R.coordinate_inverse x).2 :=
        (hnegative _).trans (by linarith)
      have hside := (hsides x hx.2).2.mpr habove
      rw [hinside x hx.1] at hside
      have hu := hfrontUpper hx.1 hside
      have hgap : L / 2 ≤ |(R.coordinate_inverse x).2| :=
        hheight.trans (le_abs_self _)
      have hd : ENNReal.ofReal ((49005 : ℝ) / 100000 * N.scale * L) ≤
          g.edist x R.center := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans (hnewLower hx.2)
        calc
          _ = ((9801 : ℝ) / 10000 * N.scale) * (L / 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
      have hstrict : ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) <
          ENNReal.ofReal ((49005 : ℝ) / 100000 * N.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith [mul_pos hr hL]
      exact (not_le_of_gt hstrict) (hd.trans hu)
    refine ⟨⟨hx.1, hOld, (N.coordinate_inverse_mem x hx.1).2.2⟩,
      hx.2, ?_, hNew⟩
    simpa only [heR] using (R.coordinate_inverse_mem x hx.2).2.1
  have hfrontier := hfront N N' hNF hepsilon hy hyout
  refine ⟨R, hchoice, hselected, ?_, ?_, ?_, hoverlap, ?_, ?_⟩
  · intro hcenters
    apply hyout
    rw [← hcR, ← hcenters]
    exact N.central_sphere_subset N.center_on_central_sphere
  · simpa only [huR] using hinter
  · refine ⟨?_, hnewQuarter⟩
    rw [huR]
    exact hfrontier.1
  · refine ⟨-L / 2, ⟨by linarith, by linarith⟩, Set.disjoint_left.mpr ?_⟩
    intro x hxR hxN
    have hh := (hoverlap ⟨hxN.1, hxR⟩).1.2.1
    have hh' : (N.coordinate_inverse x).2 < -L / 2 := hxN.2.2
    exact (not_lt_of_ge hh.le) hh'
  · rw [hcR]
    exact hfrontier.2

end PoincareConjecture.EpsilonNeck
