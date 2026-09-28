import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrientedFrontierGraph
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphSides
import Mathlib.Analysis.SpecialFunctions.SmoothTransition











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_positive_frontier_separation :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon = N.epsilon →
      N.IsSeparating →
      N'.center ∈ closure (N.region 0 N.epsilon⁻¹) →
      N'.center ∉ N.carrier → N'.IsSeparating := by
  obtain ⟨epsilon0, hpos, hcap, horient⟩ := exists_oriented_positive_frontier_graph.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hsmall hepsilon hsep hy hyout
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := N.epsilon⁻¹
  let t := 3 * L / 4
  let r := L / 2
  let c := 3 * L / 4
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  have hr : 0 < r := half_pos hL
  have hrc : r < c := by dsimp only [r, c]; linarith
  have hcL : c < L := by dsimp only [c]; linarith
  have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    change -L < t ∧ t < L
    dsimp only [t]
    constructor <;> linarith
  obtain ⟨R, f, hchoice, hf, hdom, hquant, hgraph⟩ :=
    horient N N' hsmall hepsilon hy hyout
  have heR : R.epsilon = N.epsilon := by
    rcases hchoice with rfl | rfl <;> exact hepsilon
  have hcR : R.center = N'.center := by
    rcases hchoice with rfl | rfl <;> rfl
  have hquantL (q : UnitTwoSphere) : -(3 * L / 10) < f q ∧ f q < -(L / 5) :=
    hquant q
  have hnegative (q : UnitTwoSphere) : f q < 0 := by
    linarith [(hquantL q).2]
  change range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) =
    range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) at hgraph
  obtain ⟨a, b, ha, hb, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components hsep
  obtain ⟨H, hH, hinside, hminus, hplus, _, _⟩ :=
    N.exists_saturatedAxialHeight hsep a b ha hb
  have hout {x : M} (hxC : x ∈ connectedComponent N.center) (hx : x ∉ N.carrier) :
      H x = -L ∨ H x = L := by
    rw [← hcover] at hxC
    rcases hxC with (hxA | hxS) | hxB
    · exact Or.inl (hminus x ⟨hxA, hx⟩)
    · exact False.elim (hx (N.central_sphere_subset hxS))
    · exact Or.inr (hplus x ⟨hxB, hx⟩)
  have hyC : N'.center ∈ connectedComponent N.center :=
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
    rcases hout hyC hyout with h | h
    · linarith
    · exact h
  have hcomponent : connectedComponent R.center = connectedComponent N.center := by
    rw [hcR]
    exact (connectedComponent_eq hyC).symm
  have hRC : R.carrier ⊆ connectedComponent N.center := by
    rw [← hcomponent]
    exact R.m25_carrier_subset_connectedComponent
  have hlevel (x : M) (hxC : x ∈ connectedComponent N.center) :
      H x = t ↔ x ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) := by
    by_cases hx : x ∈ N.carrier
    · rw [hinside x hx]
      constructor
      · intro hs
        refine ⟨(N.coordinate_inverse x).1, ?_⟩
        change N.coordinate_map ((N.coordinate_inverse x).1, t) = x
        rw [← hs]
        exact N.coordinate_map_inverse hx
      · rintro ⟨q, rfl⟩
        rw [N.coordinate_inverse_map (q, t) ht]
    · have hne : H x ≠ t := by
        rcases hout hxC hx with h | h <;> dsimp only [t] <;> linarith
      refine iff_of_false hne ?_
      rintro ⟨q, hq⟩
      exact hx (hq ▸ N.coordinate_map_mem ⟨mem_univ _, ht⟩)
  have hsides := N.graph_sides_of_axial_level R H hH hinside ht
    (fun x hx => hlevel x (hRC hx)) f hf.continuous hdom hnegative hgraph
    (by rw [hcR, hyH]; dsimp only [t]; linarith)
  let chi : ℝ → ℝ := fun s => Real.smoothTransition ((c - |s|) / (c - r))
  have hchi : Continuous chi :=
    Real.smoothTransition.continuous.comp
      ((continuous_const.sub continuous_abs).div_const (c - r))
  have hchibounds (s : ℝ) : 0 ≤ chi s ∧ chi s ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hchione {s : ℝ} (hs : |s| ≤ r) : chi s = 1 := by
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ (sub_pos.mpr hrc)).mpr (by linarith)
  have hchizero {s : ℝ} (hs : c ≤ |s|) : chi s = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hrc).le)
  let K := R.coordinate_map '' (univ ×ˢ Icc (-c) c)
  have hK : IsCompact K := by
    apply R.isCompact_coordinate_slab
    · rw [heR]
      change -L < -c
      linarith
    · rw [heR]
      exact hcL
  have hKR : K ⊆ R.carrier := by
    rintro x ⟨z, hz, rfl⟩
    apply R.coordinate_map_mem
    rw [cylinderDomain, heR]
    exact ⟨mem_univ _, (neg_lt_neg hcL).trans_le hz.2.1, hz.2.2.trans_lt hcL⟩
  have hmemK {x : M} (hx : x ∈ R.carrier)
      (hs : |(R.coordinate_inverse x).2| ≤ c) : x ∈ K :=
    ⟨R.coordinate_inverse x, ⟨mem_univ _, abs_le.mp hs⟩, R.coordinate_map_inverse hx⟩
  let G : M → ℝ := fun x => if x ∈ R.carrier then
    chi (R.coordinate_inverse x).2 * ((R.coordinate_inverse x).2 - (H x - t)) else 0
  have hGzero {x : M} (hx : x ∉ K) : G x = 0 := by
    by_cases hxR : x ∈ R.carrier
    · have hs : c ≤ |(R.coordinate_inverse x).2| :=
        (lt_of_not_ge (fun h => hx (hmemK hxR h))).le
      simp only [G, if_pos hxR, hchizero hs, zero_mul]
    · simp only [G, if_neg hxR]
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ R.carrier
    · have hc := R.coordinate_inverse_smooth.continuousOn.continuousAt
        (R.carrier_open.mem_nhds hx)
      have hlocal : ContinuousAt (fun y : M => chi (R.coordinate_inverse y).2 *
          ((R.coordinate_inverse y).2 - (H y - t))) x :=
        (hchi.continuousAt.comp hc.snd).mul
          (hc.snd.sub (hH.continuousAt.sub continuousAt_const))
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [R.carrier_open.mem_nhds hx] with y hyR
      simp only [G, if_pos hyR]
    · have hxK : x ∉ K := fun h => hx (hKR h)
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hyK
      exact hGzero hyK
  let F : M → ℝ := fun x => H x - t + G x
  have hF : Continuous F := (hH.sub continuous_const).add hG
  have hblend (x : M) (hx : x ∈ R.carrier) :
      F x = (1 - chi (R.coordinate_inverse x).2) * (H x - t) +
        chi (R.coordinate_inverse x).2 * (R.coordinate_inverse x).2 := by
    simp only [F, G, if_pos hx]
    ring
  have hnear (x : M) (hx : x ∈ R.carrier)
      (hs : |(R.coordinate_inverse x).2| ≤ r) : F x = (R.coordinate_inverse x).2 := by
    simp only [F, G, if_pos hx, hchione hs, one_mul]
    ring
  have hneg (x : M) (hx : x ∈ R.carrier)
      (hs : (R.coordinate_inverse x).2 < -r) : F x < 0 := by
    have hbelow : (R.coordinate_inverse x).2 < f (R.coordinate_inverse x).1 := by
      dsimp only [r] at hs
      linarith [(hquantL (R.coordinate_inverse x).1).1]
    have hold : H x - t < 0 := sub_neg.mpr ((hsides x hx).1.mpr hbelow)
    have hsneg : (R.coordinate_inverse x).2 < 0 := by linarith
    rw [hblend x hx]
    by_cases hz : chi (R.coordinate_inverse x).2 = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hold
    · have hcp : 0 < chi (R.coordinate_inverse x).2 :=
        lt_of_le_of_ne (hchibounds _).1 (Ne.symm hz)
      exact add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hchibounds _).2) hold.le)
        (mul_neg_of_pos_of_neg hcp hsneg)
  have hposF (x : M) (hx : x ∈ R.carrier)
      (hs : r < (R.coordinate_inverse x).2) : 0 < F x := by
    have habove : f (R.coordinate_inverse x).1 < (R.coordinate_inverse x).2 := by
      linarith [hnegative (R.coordinate_inverse x).1]
    have hold : 0 < H x - t := sub_pos.mpr ((hsides x hx).2.mpr habove)
    have hspos : 0 < (R.coordinate_inverse x).2 := hr.trans hs
    rw [hblend x hx]
    by_cases hz : chi (R.coordinate_inverse x).2 = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hold
    · have hcp : 0 < chi (R.coordinate_inverse x).2 :=
        lt_of_le_of_ne (hchibounds _).1 (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr (hchibounds _).2) hold.le) (mul_pos hcp hspos)
  have hzero (x : M) (hxC : x ∈ connectedComponent N.center) :
      F x = 0 ↔ x ∈ R.central_sphere := by
    by_cases hx : x ∈ R.carrier
    · by_cases hs : |(R.coordinate_inverse x).2| ≤ r
      · rw [hnear x hx hs]
        exact ((R.mem_central_sphere_iff x).trans (and_iff_right hx)).symm
      · have hfar : r < |(R.coordinate_inverse x).2| := lt_of_not_ge hs
        have hne : (R.coordinate_inverse x).2 ≠ 0 := by
          intro heq
          rw [heq, abs_zero] at hfar
          linarith
        have hFn : F x ≠ 0 := by
          by_cases hsign : 0 ≤ (R.coordinate_inverse x).2
          · rw [abs_of_nonneg hsign] at hfar
            exact (hposF x hx hfar).ne'
          · have hsign' : (R.coordinate_inverse x).2 ≤ 0 := (lt_of_not_ge hsign).le
            rw [abs_of_nonpos hsign'] at hfar
            exact (hneg x hx (by linarith)).ne
        exact iff_of_false hFn (fun hxS => hne ((R.mem_central_sphere_iff x).mp hxS).2)
    · have hFn : F x ≠ 0 := by
        intro hz
        have hxH : H x = t := by
          simpa only [F, G, if_neg hx, add_zero, sub_eq_zero] using hz
        have hxS := (hlevel x hxC).mp hxH
        rw [hgraph] at hxS
        obtain ⟨q, hq⟩ := hxS
        exact hx (hq ▸ R.coordinate_map_mem ⟨mem_univ _, hdom q⟩)
      exact iff_of_false hFn (fun hxS => hx (R.central_sphere_subset hxS))
  let q := (R.coordinate_inverse R.center).1
  have hpoint (s : ℝ) (hs : s ∈ Ioo (-L) L) (hs0 : s ≠ 0) (hsr : |s| ≤ r) :
      R.coordinate_map (q, s) ∈ connectedComponent R.center \ R.central_sphere ∧
        F (R.coordinate_map (q, s)) = s := by
    have hsR : s ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by simpa only [heR] using hs
    have hxR := R.coordinate_map_mem (show (q, s) ∈ R.cylinderDomain from
      ⟨mem_univ _, hsR⟩)
    refine ⟨⟨R.m25_carrier_subset_connectedComponent hxR, ?_⟩, ?_⟩
    · intro hxS
      have h := ((R.mem_central_sphere_iff _).mp hxS).2
      rw [R.coordinate_inverse_map (q, s) hsR] at h
      exact hs0 h
    · rw [hnear _ hxR (by simpa only [R.coordinate_inverse_map (q, s) hsR] using hsr),
        R.coordinate_inverse_map (q, s) hsR]
  have hrL : r < L := hrc.trans hcL
  have hp := hpoint r ⟨by linarith, hrL⟩ hr.ne'
    (by rw [abs_of_pos hr])
  have hm := hpoint (-r) ⟨by linarith, by linarith⟩ (by linarith)
    (by rw [abs_neg, abs_of_pos hr])
  have hsepR : R.IsSeparating := by
    refine ⟨R.m25_component_diff_central_sphere_nonempty, ?_⟩
    intro hconn
    have hsigncover : connectedComponent R.center \ R.central_sphere ⊆
        {x | F x < 0} ∪ {x | 0 < F x} := by
      intro x hx
      have hne : F x ≠ 0 := fun h => hx.2 ((hzero x (hcomponent ▸ hx.1)).mp h)
      exact lt_or_gt_of_ne hne
    have hdisj : Disjoint {x : M | F x < 0} {x | 0 < F x} := by
      apply disjoint_left.mpr
      intro x hn hp'
      exact lt_asymm (show F x < 0 from hn) (show 0 < F x from hp')
    rcases hconn.isPreconnected.subset_or_subset
      (isOpen_lt hF continuous_const) (isOpen_lt continuous_const hF) hdisj hsigncover with
      hn | hp'
    · have hbad := hn hp.1
      change F (R.coordinate_map (q, r)) < 0 at hbad
      rw [hp.2] at hbad
      exact lt_asymm hbad hr
    · have hbad := hp' hm.1
      change 0 < F (R.coordinate_map (q, -r)) at hbad
      rw [hm.2] at hbad
      linarith
  rcases hchoice with rfl | rfl <;> exact hsepR

end PoincareConjecture.EpsilonNeck
