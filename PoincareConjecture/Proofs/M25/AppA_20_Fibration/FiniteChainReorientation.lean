import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicCuts
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SharpDepth
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal

set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff Bundle ENNReal
universe u
namespace PoincareConjecture

theorem BalancedNeckChain.exists_reflected_finite_chain_of_frontier_incidence :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        ((C.neck (i + 1)).center ∈
              closure ((C.neck i).region 0 epsilon⁻¹) ∧
            (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
          ((C.neck i).center ∈
              closure ((C.neck (i + 1)).region (-epsilon⁻¹) 0) ∧
            (C.neck i).center ∉ (C.neck (i + 1)).carrier)) →
      ∃ D : BalancedNeckChain g epsilon,
        D.shape = ChainShape.finite a b ∧
        D.source_necks = C.source_necks ∧
        D.neck = (fun i => (C.neck (a + b - i)).reverse) ∧
        (⋃ i ∈ D.shape.active, (D.neck i).carrier) =
          (⋃ i ∈ C.shape.active, (C.neck i).carrier) := by
  classical
  obtain ⟨ei, hip, hicap, heights⟩ :=
    BalancedNeckChain.exists_finite_relative_saturated_heights.{u}
  obtain ⟨es, hsp, _, scales⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ))
      (by norm_num)
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 1000 * (B0 + 1) := by positivity
  refine ⟨min ei (min es (min (1 / 10000) (1 / (1000 * (B0 + 1))))),
    lt_min hip (lt_min hsp (lt_min (by norm_num) (div_pos zero_lt_one hden))),
    (min_le_left _ _).trans hicap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape he hinc
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm (x y : M) : g.edist x y = g.edist y x := Manifold.riemannianEDist_comm
  rcases le_min_iff.mp he with ⟨hei, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hes, hrest⟩
  rcases le_min_iff.mp hrest with ⟨henum, hebudget⟩
  let L : ℝ := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hepos : 0 < epsilon := C.epsilon_eq a ha ▸ (C.neck a).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hdom (i : ℤ) (hi : i ∈ C.shape.active) {t : ℝ}
      (ht : t ∈ Ioo (-L) L) : t ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
    rw [C.epsilon_eq i hi]
    exact ht
  obtain ⟨F, hF⟩ := heights C hshape hei
  obtain ⟨_, _, _, hcuts, horder⟩ :=
    C.intrinsic_ordered_cuts_of_relative_heights hshape F hF
  let q : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
  let A : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (U \ S i t)
      ((C.neck i).coordinate_map (q i, (t - L) / 2))
  have hsublevel (i : ℤ) (hi : i ∈ C.shape.active) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      A i t = U ∩ (F i) ⁻¹' Iio t := (hcuts i hi t ht).2.1
  have hT : 3 * L / 4 ∈ Ioo (-L) L := by
    constructor <;> linarith only [hL]
  have hTpos : 3 * L / 4 ∈ Ioo (L / 2) L := by
    constructor <;> linarith only [hL]

  have hnextBelow (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
      (x : M) (hx : x ∈ (C.neck i).carrier) : F (i + 1) x < L / 2 := by
    have hav (y : M) (hy : y ∈ (C.neck i).carrier) : F (i + 1) y ≠ L / 2 := by
      by_cases hyn : y ∈ (C.neck (i + 1)).carrier
      · rw [(hF (i + 1) hn).2.1 y hyn]
        exact ne_of_lt (C.overlap_within_three_quarters i hi hn ⟨hy, hyn⟩).2.2.2
      · rcases (hF (i + 1) hn).2.2 y (hNU i hi hy) hyn with hm | hp
        · rw [hm]
          linarith only [hL]
        · rw [hp]
          linarith only [hL]
    apply (C.neck i).isConnected_carrier.isPreconnected.gt_of_ne
      ((hF (i + 1) hn).1.mono (hNU i hi)) hav ?_ hx
    have ht : -(3 * L / 4) ∈ Ioo (-L) L := by
      constructor <;> linarith only [hL]
    let z : RoundCylinderSpace := (q (i + 1), -(3 * L / 4))
    have hz : z.2 ∈ Ioo (-(C.neck (i + 1)).epsilon⁻¹) (C.neck (i + 1)).epsilon⁻¹ :=
      hdom (i + 1) hn ht
    have hyn : (C.neck (i + 1)).coordinate_map z ∈ (C.neck (i + 1)).carrier :=
      (C.neck (i + 1)).coordinate_map_mem ⟨mem_univ _, hz⟩
    have hyquarter : (C.neck (i + 1)).coordinate_map z ∈
        (C.neck (i + 1)).region (-L) (-L / 2) := by
      refine ⟨hyn, ?_⟩
      rw [(C.neck (i + 1)).coordinate_inverse_map z hz]
      change -L < -(3 * L / 4) ∧ -(3 * L / 4) < -L / 2
      constructor <;> linarith only [hL]
    refine ⟨(C.neck (i + 1)).coordinate_map z,
      (C.overlap_contains_quarters i hi hn).2 hyquarter, ?_⟩
    rw [(hF (i + 1) hn).2.1 _ hyn, (C.neck (i + 1)).coordinate_inverse_map z hz]
    change -(3 * L / 4) < L / 2
    linarith only [hL]
  have hpositive (i : ℤ) (hi : i ∈ C.shape.active) (j : ℤ)
      (hj : j ∈ C.shape.active) (hij : i < j) :
      Disjoint (C.neck i).carrier ((C.neck j).region (3 * L / 4) L) := by
    have hn : i + 1 ∈ C.shape.active := by
      apply (hactive (i + 1)).mpr
      obtain ⟨hai, hib⟩ := (hactive i).mp hi
      obtain ⟨haj, hjb⟩ := (hactive j).mp hj
      constructor <;> omega
    have hstart : (C.neck i).carrier ⊆ A (i + 1) (3 * L / 4) := by
      intro x hx
      rw [hsublevel (i + 1) hn _ hT]
      refine ⟨hNU i hi hx, ?_⟩
      have hh := hnextBelow i hi hn x hx
      change F (i + 1) x < 3 * L / 4
      linarith only [hh, hL]
    have hinside : (C.neck i).carrier ⊆ A j (3 * L / 4) := by
      by_cases heq : i + 1 = j
      · exact heq ▸ hstart
      · have hlt : i + 1 < j := by omega
        have hordered : U ∩ closure (A (i + 1) (3 * L / 4)) ⊆ A j (3 * L / 4) :=
          (horder (i + 1) hn j hj hlt _ hTpos _ hTpos).1
        exact fun x hx => hordered ⟨hNU i hi hx, subset_closure (hstart hx)⟩
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hsmall := hinside hxi
    rw [hsublevel j hj _ hT] at hsmall
    have hheight := (hF j hj).2.1 x hxj.1
    have hsmall' : F j x < 3 * L / 4 := hsmall.2
    rw [hheight] at hsmall'
    exact (not_lt_of_ge hsmall'.le) hxj.2.1
  have hsqrtLower : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [henum])
  have hsqrtUpper : Real.sqrt (1 + epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [henum]⟩
  have hB0L : B0 ≤ L / 1000 := by
    have hbudget := (le_div_iff₀ hden).mp hebudget
    have hBe : B0 * epsilon ≤ 1 / 1000 := by nlinarith only [hbudget, hepos]
    calc
      B0 ≤ (1 / 1000) / epsilon := (le_div_iff₀ hepos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring

  have hmetric (N : EpsilonNeck g) (heN : N.epsilon = epsilon) (y : M)
      (hy : y ∈ closure N.carrier) (hout : y ∉ N.carrier) (s : ℝ) (hs : 0 < s)
      (hlo : (999 : ℝ) / 1000 * s ≤ N.scale)
      (hhi : N.scale ≤ (1001 : ℝ) / 1000 * s) :
      ENNReal.ofReal ((0.99 : ℝ) * s * L) ≤ g.edist N.center y ∧
        g.edist N.center y ≤ ENNReal.ofReal ((1.01 : ℝ) * s * L) := by
    have hd := N.edist_center_closure_bounds hy hout
    rw [heN] at hd
    constructor
    · apply (ENNReal.ofReal_le_ofReal ?_).trans hd.1
      change (0.99 : ℝ) * s * L ≤ N.scale * Real.sqrt (1 - epsilon) * L
      calc
        _ ≤ ((999 / 1000) * s) * (999 / 1000) * L := by
          nlinarith only [mul_pos hs hL]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul hlo hsqrtLower (by norm_num) N.scale_pos.le) hL.le
    · apply hd.2.trans (ENNReal.ofReal_le_ofReal ?_)
      change N.scale * Real.sqrt (1 + epsilon) * (L + B0) ≤ (1.01 : ℝ) * s * L
      calc
        _ ≤ ((1001 / 1000) * s) * (1001 / 1000) * (L + B0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hhi hsqrtUpper (Real.sqrt_nonneg _) (by positivity))
            (by positivity)
        _ ≤ ((1001 / 1000) * s) * (1001 / 1000) * (L + L / 1000) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hB0L) (by positivity)
        _ ≤ _ := by nlinarith only [mul_pos hs hL]
  have hbalance (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active) :
      ENNReal.ofReal ((0.99 : ℝ) * (C.neck (i + 1)).scale * L) ≤
          g.edist (C.neck (i + 1)).center (C.neck i).center ∧
        g.edist (C.neck (i + 1)).center (C.neck i).center ≤
          ENNReal.ofReal ((1.01 : ℝ) * (C.neck (i + 1)).scale * L) := by
    rcases hinc i hi hn with ⟨hy, hout⟩ | ⟨hy, hout⟩
    · have hinter : ((C.neck (i + 1)).carrier ∩ (C.neck i).carrier).Nonempty := by
        obtain ⟨x, hxi, hxn⟩ := C.adjacent_overlap i hi hn
        exact ⟨x, hxn, hxi⟩
      have hratio := (scales (C.neck (i + 1)) (C.neck i)
        (by rw [C.epsilon_eq (i + 1) hn]; exact hes)
        (by rw [C.epsilon_eq i hi]; exact hes) hinter).2
      have hlo : (999 : ℝ) / 1000 * (C.neck (i + 1)).scale ≤ (C.neck i).scale :=
        ((lt_div_iff₀ (C.neck (i + 1)).scale_pos).mp
          (show (999 : ℝ) / 1000 < (C.neck i).scale / (C.neck (i + 1)).scale by
            linarith only [(abs_lt.mp hratio).1])).le
      have hhi : (C.neck i).scale ≤ (1001 : ℝ) / 1000 * (C.neck (i + 1)).scale :=
        ((div_lt_iff₀ (C.neck (i + 1)).scale_pos).mp
          (show (C.neck i).scale / (C.neck (i + 1)).scale < (1001 : ℝ) / 1000 by
            linarith only [(abs_lt.mp hratio).2])).le
      rw [hcomm (C.neck (i + 1)).center (C.neck i).center]
      exact hmetric (C.neck i) (C.epsilon_eq i hi) (C.neck (i + 1)).center
        (closure_mono (fun _ hx => hx.1) hy) hout (C.neck (i + 1)).scale
        (C.neck (i + 1)).scale_pos hlo hhi
    · apply hmetric (C.neck (i + 1)) (C.epsilon_eq (i + 1) hn) (C.neck i).center
        (closure_mono (fun _ hx => hx.1) hy) hout (C.neck (i + 1)).scale
        (C.neck (i + 1)).scale_pos
      · nlinarith only [(C.neck (i + 1)).scale_pos]
      · nlinarith only [(C.neck (i + 1)).scale_pos]
  let r : ℤ → ℤ := fun i => a + b - i
  have hrmem (i : ℤ) (hi : i ∈ Icc a b) : r i ∈ Icc a b := by
    obtain ⟨hai, hib⟩ := hi
    dsimp only [r]
    constructor <;> omega
  have hractive (i : ℤ) (hi : i ∈ Icc a b) : r i ∈ C.shape.active :=
    (hactive (r i)).mpr (hrmem i hi)
  have hrinvol (i : ℤ) : r (r i) = i := by dsimp only [r]; omega
  have hrstep (i : ℤ) : r i = r (i + 1) + 1 := by dsimp only [r]; omega
  let D : BalancedNeckChain g epsilon := {
    shape := ChainShape.finite a b
    neck := fun i => (C.neck (r i)).reverse
    source_necks := C.source_necks
    selected := by
      intro i hi
      obtain ⟨P, hP, heq, hscale, hcenter, hcarrier, hsphere, σ, hσ, hmap⟩ :=
        C.selected (r i) (hractive i hi)
      refine ⟨P, hP, heq, hscale, hcenter, hcarrier, hsphere, -σ, ?_, ?_⟩
      · rcases hσ with hσ | hσ
        · exact Or.inr (by rw [hσ])
        · exact Or.inl (by rw [hσ]; norm_num)
      · intro z hz
        change z.2 ∈ Ioo (-(C.neck (r i)).epsilon⁻¹)
          (C.neck (r i)).epsilon⁻¹ at hz
        change (C.neck (r i)).coordinate_map (z.1, -z.2) =
          P.coordinate_map (z.1, -σ * z.2)
        have hz' : (-z.2) ∈ Ioo (-(C.neck (r i)).epsilon⁻¹)
            (C.neck (r i)).epsilon⁻¹ := by
          change -(C.neck (r i)).epsilon⁻¹ < -z.2 ∧
            -z.2 < (C.neck (r i)).epsilon⁻¹
          constructor <;> linarith only [hz.1, hz.2]
        rw [hmap (z.1, -z.2) hz']
        congr 1
        exact Prod.ext rfl (by ring)
    active_nonempty := ⟨a, le_rfl, hab⟩
    epsilon_eq := fun i hi => C.epsilon_eq (r i) (hractive i hi)
    centers_distinct := by
      intro i hi j hj hij
      change (C.neck (r i)).center ≠ (C.neck (r j)).center
      apply C.centers_distinct (hractive i hi) (hractive j hj)
      intro heq
      have hh := congrArg r heq
      have heq' : i = j := by simpa only [hrinvol] using hh
      exact hij heq'
    adjacent_overlap := by
      intro i hi hn
      have hlo := hractive (i + 1) hn
      have hhi := hractive i hi
      have hnext : r (i + 1) + 1 ∈ C.shape.active := hrstep i ▸ hhi
      obtain ⟨x, hxlo, hxhi⟩ := C.adjacent_overlap (r (i + 1)) hlo hnext
      rw [← hrstep i] at hxhi
      exact ⟨x, hxhi, hxlo⟩
    overlap_contains_quarters := by
      intro i hi hn
      have hlo := hractive (i + 1) hn
      have hhi := hractive i hi
      have hnext : r (i + 1) + 1 ∈ C.shape.active := hrstep i ▸ hhi
      have hq := C.overlap_contains_quarters (r (i + 1)) hlo hnext
      rw [← hrstep i] at hq
      constructor
      · change (C.neck (r i)).reverse.region (epsilon⁻¹ / 2) epsilon⁻¹ ⊆
          (C.neck (r (i + 1))).carrier
        simpa only [EpsilonNeck.reverse_region, neg_div] using hq.2
      · change (C.neck (r (i + 1))).reverse.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ⊆
          (C.neck (r i)).carrier
        simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using hq.1
    overlap_within_three_quarters := by
      intro i hi hn x hx
      have hlo := hractive (i + 1) hn
      have hhi := hractive i hi
      have hnext : r (i + 1) + 1 ∈ C.shape.active := hrstep i ▸ hhi
      have ho := C.overlap_within_three_quarters (r (i + 1)) hlo hnext
      rw [← hrstep i] at ho
      have hh := ho ⟨hx.2, hx.1⟩
      constructor
      · change x ∈ (C.neck (r i)).carrier ∧
          -L / 2 < -((C.neck (r i)).coordinate_inverse x).2 ∧
          -((C.neck (r i)).coordinate_inverse x).2 < L
        exact ⟨hx.1, by linarith only [hh.2.2.2], by linarith only [hh.2.2.1]⟩
      · change x ∈ (C.neck (r (i + 1))).carrier ∧
          -L < -((C.neck (r (i + 1))).coordinate_inverse x).2 ∧
          -((C.neck (r (i + 1))).coordinate_inverse x).2 < L / 2
        exact ⟨hx.2, by linarith only [hh.1.2.2], by linarith only [hh.1.2.1]⟩
    later_disjoint_negative_end := by
      intro i hi j hj hij
      have hji : r j < r i := by dsimp only [r]; omega
      refine ⟨-(3 * L / 4), ⟨by linarith only [hL], by linarith only [hL]⟩, ?_⟩
      change Disjoint (C.neck (r j)).carrier
        ((C.neck (r i)).reverse.region (-L) (-(3 * L / 4)))
      simpa only [EpsilonNeck.reverse_region, neg_neg] using
        hpositive (r j) (hractive j hj) (r i) (hractive i hi) hji
    balanced_center_distance := by
      intro i hi hn
      have hlo := hractive (i + 1) hn
      have hhi := hractive i hi
      have hnext : r (i + 1) + 1 ∈ C.shape.active := hrstep i ▸ hhi
      have hd := hbalance (r (i + 1)) hlo hnext
      rw [← hrstep i] at hd
      exact hd }
  refine ⟨D, rfl, rfl, rfl, ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨r i, hractive i hi, hxi⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨r i, hrmem i ((hactive i).mp hi), ?_⟩
    change x ∈ (C.neck (r (r i))).carrier
    rw [hrinvol]
    exact hxi

end PoincareConjecture
