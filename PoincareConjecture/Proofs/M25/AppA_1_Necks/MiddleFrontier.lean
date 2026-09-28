import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveFrontier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Reversal











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain



theorem exists_middle_region_closure_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      closure (⋃ i ∈ C.shape.active,
        (C.neck i).region (-(3 * epsilon⁻¹ / 4)) (3 * epsilon⁻¹ / 4)) ⊆
        ⋃ i ∈ C.shape.active, (C.neck i).carrier := by
  obtain ⟨epsilon0, he0, hecap, hcontrol⟩ :=
    EpsilonNeck.exists_normalized_scalar_control_on_carrier.{u} (α := 1 / 2) (by norm_num)
  refine ⟨epsilon0, he0, hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C he x hx
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  by_contra hxout
  obtain ⟨i0, hi0⟩ := C.active_nonempty
  let D := (C.neck i0).connection
  let L := epsilon⁻¹
  have hepos : 0 < epsilon := C.epsilon_eq i0 hi0 ▸ (C.neck i0).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hroot : 0 < Real.sqrt (1 - epsilon) := Real.sqrt_pos.mpr (by linarith [he.trans hecap])
  have hscalar (N : EpsilonNeck g) (z : M) :
      N.connection.scalarCurvature z = D.scalarCurvature z := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [N.connection.horizon_curvatureTensor_eq D z]
  let K := |D.scalarCurvature x| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  let rho := Real.sqrt (1 / (2 * K))
  have hrho : 0 < rho := Real.sqrt_pos.mpr (by positivity)
  have hrhosq : rho ^ 2 = 1 / (2 * K) := Real.sq_sqrt (by positivity)
  have hrhoK : rho ^ 2 * K = 1 / 2 := by
    rw [hrhosq]
    field_simp
  have hscale {i : ℤ} (hi : i ∈ C.shape.active) {z : M}
      (hz : z ∈ (C.neck i).carrier) (hzK : D.scalarCurvature z < K) :
      rho ≤ (C.neck i).scale := by
    have h := hcontrol (C.neck i) (by rw [C.epsilon_eq i hi]; exact he) z hz
    rw [hscalar] at h
    have hlower : (1 : ℝ) / 2 < (C.neck i).scale ^ 2 * D.scalarCurvature z := by
      linarith [(abs_lt.mp h).1]
    have hupper := mul_lt_mul_of_pos_left hzK (sq_pos_of_pos (C.neck i).scale_pos)
    by_contra hn
    have hsq : (C.neck i).scale ^ 2 < rho ^ 2 :=
      (sq_lt_sq₀ (C.neck i).scale_pos.le hrho.le).mpr (lt_of_not_ge hn)
    have hprod := mul_lt_mul_of_pos_right hsq hK
    rw [hrhoK] at hprod
    linarith
  let d := rho * Real.sqrt (1 - epsilon) * (L / 4)
  have hd : 0 < d := mul_pos (mul_pos hrho hroot) (div_pos hL (by norm_num))
  let W := {z | D.scalarCurvature z < K} ∩ {z | g.edist z x < ENNReal.ofReal d}
  have hW : IsOpen W :=
    (isOpen_lt D.continuous_scalarCurvature continuous_const).inter
      (isOpen_lt (continuous_id.edist continuous_const) continuous_const)
  have hxW : x ∈ W := by
    refine ⟨?_, ?_⟩
    · change D.scalarCurvature x < |D.scalarCurvature x| + 1
      linarith [le_abs_self (D.scalarCurvature x)]
    · change edist x x < ENNReal.ofReal d
      simpa only [edist_self] using ENNReal.ofReal_pos.mpr hd
  obtain ⟨z, hzW, hzV⟩ := mem_closure_iff.mp hx W hW hxW
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzV
  have hxis : x ∉ (C.neck i).carrier := by
    intro hxi
    exact hxout (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
  have hscalei := hscale hi hzi.1 hzW.1
  have haxis : |((C.neck i).coordinate_inverse z).2| < 3 * L / 4 :=
    abs_lt.mpr hzi.2
  have hdepth : L / 4 ≤ L - |((C.neck i).coordinate_inverse z).2| := by linarith
  have hdepthpos : 0 < L - |((C.neck i).coordinate_inverse z).2| := by linarith
  have hlower := (C.neck i).axialDepth_edist_le z x
  simp only [EpsilonNeck.axialDepth, if_pos hzi.1, if_neg hxis, sub_zero,
    C.epsilon_eq i hi] at hlower
  rw [abs_of_pos hdepthpos] at hlower
  have hdle : d ≤ (C.neck i).scale * Real.sqrt (1 - epsilon) *
      (L - |((C.neck i).coordinate_inverse z).2|) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hscalei hroot.le) hdepth
      (by positivity) (mul_nonneg (C.neck i).scale_pos.le hroot.le)
  exact (not_le_of_gt hzW.2) ((ENNReal.ofReal_le_ofReal hdle).trans hlower)



theorem exists_frontier_subset_exposed_end_closures :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        ((C.neck (i + 1)).center ∈
              closure ((C.neck i).region 0 epsilon⁻¹) ∧
            (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
          ((C.neck i).center ∈
              closure ((C.neck (i + 1)).region (-epsilon⁻¹) 0) ∧
            (C.neck i).center ∉ (C.neck (i + 1)).carrier)) →
      frontier (⋃ i ∈ C.shape.active, (C.neck i).carrier) ⊆
        match C.shape with
        | .finite a b =>
            closure ((C.neck a).region (-epsilon⁻¹) 0) ∪
              closure ((C.neck b).region 0 epsilon⁻¹)
        | .forward a => closure ((C.neck a).region (-epsilon⁻¹) 0)
        | .backward b => closure ((C.neck b).region 0 epsilon⁻¹)
        | .biInfinite => ∅ := by
  obtain ⟨epsilonM, hM, hMcap, hmiddle⟩ := exists_middle_region_closure_control.{u}
  obtain ⟨epsilonS, hS, _, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := 1 / 100) (by norm_num)
  let B := Real.sqrt 2 * (Real.pi + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hden : 0 < 1000 * (B + 1) := by positivity
  refine ⟨min epsilonM (min epsilonS (1 / (1000 * (B + 1)))),
    lt_min hM (lt_min hS (div_pos zero_lt_one hden)),
    (min_le_left _ _).trans hMcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C he hincidence
  classical
  obtain ⟨i0, hi0⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i0 hi0 ▸ (C.neck i0).epsilon_pos
  let L := epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr hepos
  have heM : epsilon ≤ epsilonM := he.trans (min_le_left _ _)
  have heS : epsilon ≤ epsilonS :=
    (he.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hecap : epsilon ≤ 1 / 200 := heM.trans hMcap
  have hsmall : epsilon ≤ 1 / (1000 * (B + 1)) :=
    (he.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hBL : B ≤ L / 1000 := by
    have h := (le_div_iff₀ hden).mp hsmall
    have hBe : B * epsilon ≤ 1 / 1000 := by nlinarith
    calc
      B ≤ (1 / 1000) / epsilon := (le_div_iff₀ hepos).mpr hBe
      _ = L / 1000 := by dsimp only [L]; ring
  have hb : (99 : ℝ) / 100 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hp : Real.sqrt (1 + epsilon) ≤ (101 : ℝ) / 100 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hpair (N R : EpsilonNeck g) (hNe : N.epsilon = epsilon)
      (hRe : R.epsilon = epsilon) (hinter : (N.carrier ∩ R.carrier).Nonempty)
      (hQ : N.region (L / 2) L ⊆ R.carrier ∧
        R.region (-L) (-L / 2) ⊆ N.carrier)
      (hwithin : N.carrier ∩ R.carrier ⊆
        N.region (-L / 2) L ∩ R.region (-L) (L / 2))
      (hy : R.center ∈ closure (N.region 0 L)) (hyout : R.center ∉ N.carrier) :
      N.region (L / 2) L ⊆ R.region (-(3 * L / 4)) (3 * L / 4) ∧
      R.region (-L) (-L / 2) ⊆ N.region (-(3 * L / 4)) (3 * L / 4) := by
    have hr : 0 < N.scale := N.scale_pos
    have hratio := (hscale N R (by rw [hNe]; exact heS)
      (by rw [hRe]; exact heS) hinter).2
    have hscaleLower : (99 : ℝ) / 100 * N.scale ≤ R.scale :=
      ((lt_div_iff₀ N.scale_pos).mp
        (show (99 : ℝ) / 100 < R.scale / N.scale by
          linarith [(abs_lt.mp hratio).1])).le
    have hprodLower : (9801 : ℝ) / 10000 * N.scale ≤
        R.scale * Real.sqrt (1 - epsilon) := by
      calc
        _ = ((99 / 100) * N.scale) * (99 / 100) := by ring
        _ ≤ _ := mul_le_mul hscaleLower hb (by norm_num) R.scale_pos.le
    have hc := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
    have hnewLower {z : M} (hz : z ∈ R.carrier) :
        ENNReal.ofReal ((9801 : ℝ) / 10000 * N.scale * |(R.coordinate_inverse z).2|) ≤
          g.edist z R.center := by
      have hdiff : R.axialDepth z - R.axialDepth R.center =
          -|(R.coordinate_inverse z).2| := by
        simp only [EpsilonNeck.axialDepth, if_pos hz, if_pos hc.1, hc.2,
          abs_zero, sub_zero]
        ring
      have hd := R.axialDepth_edist_le z R.center
      rw [hdiff, abs_neg, abs_abs, hRe] at hd
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hprodLower (abs_nonneg _))).trans hd
    have hupper {z : M} (hz : z ∈ N.carrier) {t : ℝ} (ht : 0 < t)
        (hheight : L - (N.coordinate_inverse z).2 ≤ t * L) :
        g.edist z R.center ≤
          ENNReal.ofReal (N.scale * (101 / 100) * (t * L + L / 1000)) := by
      have hu := N.edist_le_positive_frontier hz (by simpa only [hNe] using hy) hyout
      rw [hNe] at hu
      apply hu.trans (ENNReal.ofReal_le_ofReal ?_)
      change N.scale * Real.sqrt (1 + epsilon) *
        (L - (N.coordinate_inverse z).2 + B) ≤ _
      calc
        _ ≤ N.scale * Real.sqrt (1 + epsilon) * (t * L + B) :=
          mul_le_mul_of_nonneg_left (add_le_add hheight le_rfl)
            (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
        _ ≤ N.scale * (101 / 100) * (t * L + B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp N.scale_pos.le)
            (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hBL) (by positivity)
    constructor
    · intro z hz
      have hzR := hQ.1 hz
      refine ⟨hzR, ?_⟩
      apply abs_lt.mp
      by_contra hn
      have hlarge : 3 * L / 4 ≤ |(R.coordinate_inverse z).2| := le_of_not_gt hn
      have hu : g.edist z R.center ≤
          ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) := by
        convert hupper hz.1 (t := 1 / 2) (by norm_num) (by linarith [hz.2.1]) using 1
        congr 1
        ring
      have hd : ENNReal.ofReal ((735075 : ℝ) / 1000000 * N.scale * L) ≤
          g.edist z R.center := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans (hnewLower hzR)
        calc
          _ = ((9801 : ℝ) / 10000 * N.scale) * (3 * L / 4) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (by positivity)
      have hstrict : ENNReal.ofReal ((50601 : ℝ) / 100000 * N.scale * L) <
          ENNReal.ofReal ((735075 : ℝ) / 1000000 * N.scale * L) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        nlinarith [mul_pos N.scale_pos hL]
      exact (not_le_of_gt hstrict) (hd.trans hu)
    · intro z hz
      have hzN := hQ.2 hz
      have hover := hwithin ⟨hzN, hz.1⟩
      refine ⟨hzN, by linarith [hover.1.2.1], ?_⟩
      by_contra hn
      have hhigh : 3 * L / 4 ≤ (N.coordinate_inverse z).2 := le_of_not_gt hn
      have hu : g.edist z R.center ≤
          ENNReal.ofReal ((25351 : ℝ) / 100000 * N.scale * L) := by
        convert hupper hzN (t := 1 / 4) (by norm_num) (by linarith) using 1
        congr 1
        ring
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
  have htransfer (i : ℤ) (hi : i ∈ C.shape.active) (hinext : i + 1 ∈ C.shape.active) :
      (C.neck i).region (L / 2) L ⊆
          (C.neck (i + 1)).region (-(3 * L / 4)) (3 * L / 4) ∧
        (C.neck (i + 1)).region (-L) (-L / 2) ⊆
          (C.neck i).region (-(3 * L / 4)) (3 * L / 4) := by
    have hQ := C.overlap_contains_quarters i hi hinext
    have hwithin := C.overlap_within_three_quarters i hi hinext
    rcases hincidence i hi hinext with hforward | hbackward
    · exact hpair (C.neck i) (C.neck (i + 1))
        (C.epsilon_eq i hi) (C.epsilon_eq (i + 1) hinext)
        (C.adjacent_overlap i hi hinext) hQ hwithin hforward.1 hforward.2
    · have hinter : ((C.neck (i + 1)).reverse.carrier ∩
          (C.neck i).reverse.carrier).Nonempty := by
        simpa only [EpsilonNeck.reverse, inter_comm] using C.adjacent_overlap i hi hinext
      have hQr : (C.neck (i + 1)).reverse.region (L / 2) L ⊆
          (C.neck i).reverse.carrier ∧
          (C.neck i).reverse.region (-L) (-L / 2) ⊆
          (C.neck (i + 1)).reverse.carrier := by
        constructor
        · change (C.neck (i + 1)).reverse.region (L / 2) L ⊆ (C.neck i).carrier
          rw [EpsilonNeck.reverse_region]
          simpa only [neg_div, L] using hQ.2
        · change (C.neck i).reverse.region (-L) (-L / 2) ⊆ (C.neck (i + 1)).carrier
          rw [EpsilonNeck.reverse_region]
          simpa only [neg_div, neg_neg, L] using hQ.1
      have hwr : (C.neck (i + 1)).reverse.carrier ∩ (C.neck i).reverse.carrier ⊆
          (C.neck (i + 1)).reverse.region (-L / 2) L ∩
            (C.neck i).reverse.region (-L) (L / 2) := by
        intro z hz
        have hw := hwithin ⟨hz.2, hz.1⟩
        constructor
        · simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using hw.2
        · simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using hw.1
      have hyr : (C.neck i).reverse.center ∈
          closure ((C.neck (i + 1)).reverse.region 0 L) := by
        change (C.neck i).center ∈ closure ((C.neck (i + 1)).reverse.region 0 L)
        rw [EpsilonNeck.reverse_region]
        simpa only [neg_zero, L] using hbackward.1
      have h := hpair (C.neck (i + 1)).reverse (C.neck i).reverse
        (C.epsilon_eq (i + 1) hinext) (C.epsilon_eq i hi)
        hinter hQr hwr hyr hbackward.2
      constructor
      · simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using h.2
      · simpa only [EpsilonNeck.reverse_region, neg_div, neg_neg] using h.1
  let U := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let V := ⋃ i ∈ C.shape.active, (C.neck i).region (-(3 * L / 4)) (3 * L / 4)
  let E : Set M := match C.shape with
    | .finite a b => closure ((C.neck a).region (-L) 0) ∪
        closure ((C.neck b).region 0 L)
    | .forward a => closure ((C.neck a).region (-L) 0)
    | .backward b => closure ((C.neck b).region 0 L)
    | .biInfinite => ∅
  have hE : IsClosed E := by
    cases hs : C.shape <;> simp only [E, hs]
    · exact isClosed_closure.union isClosed_closure
    · exact isClosed_closure
    · exact isClosed_closure
    · exact isClosed_empty
  have hcover : U ⊆ V ∪ E := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    have hcoord := (C.neck i).coordinate_inverse_mem z hzi
    rw [C.epsilon_eq i hi] at hcoord
    by_cases hlower : -(3 * L / 4) < ((C.neck i).coordinate_inverse z).2
    · by_cases hupper : ((C.neck i).coordinate_inverse z).2 < 3 * L / 4
      · exact Or.inl (mem_iUnion₂.mpr ⟨i, hi, hzi, hlower, hupper⟩)
      have hpos : z ∈ (C.neck i).region (L / 2) L :=
        ⟨hzi, by linarith, hcoord.2.2⟩
      by_cases hn : i + 1 ∈ C.shape.active
      · exact Or.inl (mem_iUnion₂.mpr ⟨i + 1, hn, (htransfer i hi hn).1 hpos⟩)
      have hhalf : z ∈ closure ((C.neck i).region 0 L) :=
        subset_closure ⟨hzi, by linarith [hpos.2.1], hcoord.2.2⟩
      right
      cases hs : C.shape with
      | finite a b =>
          have hii : i ∈ Icc a b := by simpa only [hs, ChainShape.active] using hi
          have hnn : ¬i + 1 ∈ Icc a b := by simpa only [hs, ChainShape.active] using hn
          have hib : i = b := by rcases hii with ⟨_, _⟩; simp only [mem_Icc] at hnn; omega
          simpa only [E, hs, hib, mem_union] using Or.inr hhalf
      | forward a =>
          have hii : a ≤ i := by simpa only [hs, ChainShape.active, mem_Ici] using hi
          exact False.elim (hn (by simpa only [hs, ChainShape.active, mem_Ici] using
            (show a ≤ i + 1 by omega)))
      | backward b =>
          have hii : i ≤ b := by simpa only [hs, ChainShape.active, mem_Iic] using hi
          have hnn : ¬i + 1 ≤ b := by simpa only [hs, ChainShape.active, mem_Iic] using hn
          have hib : i = b := by omega
          simpa only [E, hs, hib] using hhalf
      | biInfinite => exact False.elim (hn (by simp only [hs, ChainShape.active, mem_univ]))
    · have hneg : z ∈ (C.neck i).region (-L) (-L / 2) :=
        ⟨hzi, hcoord.2.1, by linarith⟩
      by_cases hp : i - 1 ∈ C.shape.active
      · have hnext : i - 1 + 1 ∈ C.shape.active := by simpa only [sub_add_cancel] using hi
        have hprev := (htransfer (i - 1) hp hnext).2
        rw [sub_add_cancel] at hprev
        exact Or.inl (mem_iUnion₂.mpr ⟨i - 1, hp, hprev hneg⟩)
      have hhalf : z ∈ closure ((C.neck i).region (-L) 0) :=
        subset_closure ⟨hzi, hcoord.2.1, by linarith [hneg.2.2]⟩
      right
      cases hs : C.shape with
      | finite a b =>
          have hii : i ∈ Icc a b := by simpa only [hs, ChainShape.active] using hi
          have hpp : ¬i - 1 ∈ Icc a b := by simpa only [hs, ChainShape.active] using hp
          have hia : i = a := by rcases hii with ⟨_, _⟩; simp only [mem_Icc] at hpp; omega
          simpa only [E, hs, hia, mem_union] using Or.inl hhalf
      | forward a =>
          have hii : a ≤ i := by simpa only [hs, ChainShape.active, mem_Ici] using hi
          have hpp : ¬a ≤ i - 1 := by simpa only [hs, ChainShape.active, mem_Ici] using hp
          have hia : i = a := by omega
          simpa only [E, hs, hia] using hhalf
      | backward b =>
          have hii : i ≤ b := by simpa only [hs, ChainShape.active, mem_Iic] using hi
          exact False.elim (hp (by simpa only [hs, ChainShape.active, mem_Iic] using
            (show i - 1 ≤ b by omega)))
      | biInfinite => exact False.elim (hp (by simp only [hs, ChainShape.active, mem_univ]))
  have hU : IsOpen U := isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (C.neck i).carrier_open))
  intro x hx
  have hout : x ∉ U := by
    have h := hx.2
    change x ∉ interior U at h
    simpa only [hU.interior_eq] using h
  have hmem := closure_mono hcover hx.1
  rw [closure_union, hE.closure_eq] at hmem
  exact hmem.resolve_left (fun h => hout (hmiddle C heM h))

end PoincareConjecture.BalancedNeckChain
