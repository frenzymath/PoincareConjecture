import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerModels
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SubsetCenterSelection
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.RiemannianLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SubsetSpires
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiberRebase
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RadiusConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.ExpandingSubsetSpireCenters
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberCompact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

open Set Filter Topology MeasureTheory Function
open PoincareConjecture Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle

private theorem corner_boundedFiberSection_isCompact
    {m k : ℕ} {δ H : ℝ} (A : PointedCornerModel m k δ H) :
    IsCompact A.boundedFiberSection := by
  let : Nonempty A.carrier := ⟨A.ambientPoint⟩
  let : MetricSpace A.carrier := A.metric.toMetricSpace
  have hcompact := A.metric.isCompact_openFiber_preimage_closedBall A.complete
    A.joint_smooth.continuous A.domain A.value A.ambientPoint (3/2)
    (fun y hy => A.buffer y (hy.trans (ENNReal.ofReal_le_ofReal (by norm_num))))
  have he : {z : openFiber A.joint A.domain A.value |
      (A.metric.edist A.ambientPoint (openFiberIncl A.joint A.domain A.value z)).toReal ≤ 3/2} =
      {z : openFiber A.joint A.domain A.value |
        A.metric.edist A.ambientPoint (openFiberIncl A.joint A.domain A.value z) ≤
          ENNReal.ofReal (3/2)} := by
    ext z
    change _ ≤ (3/2 : ℝ) ↔ _ ≤ ENNReal.ofReal (3/2)
    constructor
    · intro hz
      rw [← ENNReal.ofReal_toReal (A.metric.edist_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hz
    · exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
  rw [PointedCornerModel.boundedFiberSection,he]
  exact hcompact.image (isEmbedding_openFiberIncl A.joint A.domain A.value).continuous

theorem PoincareConjecture.exists_corner_spire_centers_of_expanding_limit
    {m k : ℕ} {δ H : ℝ} (A : ℕ → PoincareConjecture.PointedCornerModel m k δ H)
    (T : CompatiblePointedCompactSystem.{0})
    (K : TopologicalSpace.NonemptyCompacts T.completedLimit.carrier)
    (hlim : PoincareConjecture.IsExpandingCornerLimit A T K)
    {cminus c cplus cap : ℝ}
    (hminus0 : 0 ≤ cminus) (hminus : cminus < c)
    (hplus : c < cplus) (hplus1 : cplus < 1) (hcap : 0 < cap) :
    let Y := T.completedLimit
    let incl := fun j => openFiberIncl (A j).joint (A j).domain (A j).value
    ∃ s t ε : ℕ → ℝ,
      Tendsto s atTop atTop ∧ Tendsto t atTop atTop ∧
      (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ hs : ∀ j, (3/2 : ℝ) < s j, ∃ ht : ∀ j, (3/2 : ℝ) < t j,
      ∃ Q : ∀ j, PointedGHRealization
        (ballModel (A j).basedSpace (s j) ((by norm_num : (0:ℝ)<3/2).trans (hs j)))
        (ballModel Y (t j) ((by norm_num : (0:ℝ)<3/2).trans (ht j))),
        Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0) ∧
        ∃ hK : (K : Set Y.carrier) ⊆ Metric.closedBall Y.base (3/2),
        (∀ j (x : (A j).boundedFiberSection), ∃ y : K,
          dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr
            (((A j).boundedFiberSection_dist_le x.val x.property).trans_lt (hs j))⟩)
            ((Q j).right ⟨y.val, Metric.mem_ball.mpr
              ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) ∧
        (∀ j (y : K), ∃ x : (A j).boundedFiberSection,
          dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr
            (((A j).boundedFiberSection_dist_le x.val x.property).trans_lt (hs j))⟩)
            ((Q j).right ⟨y.val, Metric.mem_ball.mpr
              ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) ∧
        ∃ (B : Y.carrier → ℝ) (P S : Finset Y.carrier) (b ρ : ℝ),
          (∀ x, 0 < B x ∧ 2*B x ≤ cap) ∧
          (∀ x y : Y.carrier, 0 < dist x y → dist x y < 2*B x →
            HasLocalDistanceAscent cminus x y) ∧
          (∀ x : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2*a ≤ cap →
            (∀ y : Y.carrier, 0 < dist x y → dist x y < 2*a →
              HasLocalDistanceAscent cminus x y) → a ≤ B x) ∧
          (P : Set Y.carrier) ⊆ K ∧
          ∃ hSK : (S : Set Y.carrier) ⊆ K,
          (S : Set Y.carrier) =
            {x | x ∈ K ∧ ∀ y ∈ K, y ≠ x → B y/4 ≤ dist y x} ∧
          (K : Set Y.carrier) \ (S : Set Y.carrier) ⊆
            ⋃ y ∈ P, Metric.ball y (B y/4) \ {y} ∧
          0 < b ∧ b ≤ cap ∧ 0 < ρ ∧ ρ < b/8 ∧
          (∀ i : S, ∀ y : Y.carrier, 0 < dist i.val y → dist i.val y ≤ 2*b →
            HasLocalDistanceAscent cplus i.val y) ∧
          ∃ (ref : ∀ j, K → openFiber (A j).joint (A j).domain (A j).value)
            (q : ∀ j, S → openFiber (A j).joint (A j).domain (A j).value),
          ∃ href : ∀ j y, ((A j).metric.edist (A j).ambientPoint (incl j (ref j y))).toReal ≤ 3/2,
          (∀ j y,
            dist ((Q j).left ⟨incl j (ref j y), Metric.mem_ball'.mpr ((href j y).trans_lt (hs j))⟩)
              ((Q j).right ⟨y.val, Metric.mem_ball.mpr
                ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) ∧
          (∀ y z : K,
            Tendsto (fun j => ((A j).metric.edist (incl j (ref j y)) (incl j (ref j z))).toReal)
              atTop (𝓝 (dist y.val z.val))) ∧
          (∀ y : K,
            Tendsto (fun j => ((A j).metric.edist (A j).ambientPoint (incl j (ref j y))).toReal)
              atTop (𝓝 (dist Y.base y.val)) ∧
            PointedGHConvergesUnbounded
              (fun j => (A j).metric.toBasedMetricSpace (incl j (ref j y))) (Y.rebase y.val)) ∧
          (∀ j i, ((A j).metric.edist (A j).ambientPoint (incl j (q j i))).toReal ≤ 3/2) ∧
          (∀ j (i : S), letI := (A j).metric.toMetricSpace
            let v := incl j (ref j ⟨i.val,hSK i.property⟩)
            dist v (incl j (q j i)) ≤ ρ ∧
            badAscentRadius c b (incl j (q j i)) ≤ badAscentRadius c b v ∧
            ∀ z ∈ (A j).boundedFiberSection, dist v z ≤ ρ →
              badAscentRadius c b (incl j (q j i)) ≤ 2*badAscentRadius c b z) ∧
          ∀ i : S,
            Tendsto (fun j => letI := (A j).metric.toMetricSpace
              badAscentRadius c b (incl j (ref j ⟨i.val,hSK i.property⟩))) atTop (𝓝 0) ∧
            Tendsto (fun j => letI := (A j).metric.toMetricSpace
              badAscentRadius c b (incl j (q j i))) atTop (𝓝 0) ∧
            Tendsto (fun j => ((A j).metric.edist
              (incl j (ref j ⟨i.val,hSK i.property⟩)) (incl j (q j i))).toReal) atTop (𝓝 0) ∧
            PointedGHConvergesUnbounded
              (fun j => (A j).metric.toBasedMetricSpace (incl j (q j i))) (Y.rebase i.val) := by
  classical
  let Y := T.completedLimit
  let incl := fun j => openFiberIncl (A j).joint (A j).domain (A j).value
  let g := fun j => (A j).metric
  let D := fun j => (A j).connection
  let p := fun j => (A j).ambientPoint
  let E := fun j => (A j).boundedFiberSection
  let (j : ℕ) : MetricSpace (A j).carrier := (A j).metric.toMetricSpace
  obtain ⟨hproper,hgeo,hconv,s,t,ε,hsTop,htTop,hεpos,hε,hs,ht,Q,hQ,hK,hbase,
    hforward,hback⟩ := hlim
  let : ProperSpace Y.carrier := hproper
  let (j : ℕ) : ProperSpace (A j).basedSpace.carrier :=
    (A j).metric.properSpace_toMetricSpace (A j).complete
  have hc : 0 ≤ c := hminus0.trans hminus.le
  have hplus0 : 0 ≤ cplus := hc.trans hplus.le
  have hc1 : c < 1 := hplus.trans hplus1
  have hminus1 : cminus < 1 := hminus.trans hc1
  have hY := RiemannianMetric.curvatureGEnegOne_of_sectional_pointed_limit
    g p D (fun j => (A j).complete) (fun j => (A j).sectional_lower) hconv
  have hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ,
      ComparisonAnglePackingBound Y.carrier α N := by
    intro α hα
    obtain ⟨N,hN⟩ := RiemannianMetric.exists_comparisonAngle_packing_bound_of_sectional_pointed_limit
      (m+k) hα
    exact ⟨N,hN g p D (fun j => (A j).complete) (fun j => (A j).sectional_lower) hconv⟩
  obtain ⟨B,hB,hBasc,hBmax⟩ := exists_maximal_regular_radius_function
    hY hgeo hpacking hminus0 hminus1 hcap
  obtain ⟨P,S,hPK,hSK,hS,hcover⟩ := exists_finite_punctured_ball_cover_on_subset
    K.isCompact (fun x => B x/4) (fun x _ => div_pos (hB x).1 (by norm_num))
  obtain ⟨Bplus,hBplus,hBplusAsc,_⟩ := exists_maximal_regular_radius_function
    hY hgeo hpacking hplus0 hplus1 hcap
  let J : Finset ℝ := insert cap (S.image (fun i => Bplus i/2))
  have hJ : J.Nonempty := ⟨cap,by simp [J]⟩
  let b := J.min' hJ
  have hb : 0 < b := by
    have hmem : b ∈ J := Finset.min'_mem J hJ
    rcases Finset.mem_insert.mp hmem with h | h
    · simpa only [h] using hcap
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      simpa only [hi] using half_pos (hBplus i).1
  have hbcap : b ≤ cap := Finset.min'_le J cap (by simp [J])
  have hbi (i : S) : b ≤ Bplus i.val/2 :=
    Finset.min'_le J (Bplus i.val/2) (by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩)
  let ρ := b/16
  have hρ : 0 < ρ := div_pos hb (by norm_num)
  have hρb : ρ < b/8 := by dsimp [ρ]; linarith
  have hstrong (i : S) (y : Y.carrier) (hy : 0 < dist i.val y)
      (hyb : dist i.val y ≤ 2*b) : HasLocalDistanceAscent cplus i.val y := by
    apply hBplusAsc i.val y hy
    have hi := hbi i
    have hipos := (hBplus i.val).1
    linarith
  have hrefs := RiemannianMetric.exists_openFiber_lifts_rebased_limit_of_expanding_realizations
    g (fun j => (A j).complete) (fun j => (A j).joint) (fun j => (A j).domain)
    (fun j => (A j).value) (fun j => (A j).point) hgeo
    (by norm_num : (0:ℝ) ≤ 3/2) hs ht hsTop htTop hε Q hQ K hK hback
  choose v hv hmark hrad hvconv using hrefs
  let ref := fun j y => v y j
  have href (j : ℕ) (y : K) :
      ((A j).metric.edist (A j).ambientPoint (incl j (ref j y))).toReal ≤ 3/2 := hv y j
  have hrefE (j : ℕ) (y : K) : incl j (ref j y) ∈ E j := ⟨ref j y,href j y,rfl⟩
  have hXgeo (j : ℕ) (x y : (A j).basedSpace.carrier) :
      ∃ γ : ℝ → (A j).basedSpace.carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1,
          dist (γ a) (γ b) = |a-b| *dist x y := by
    obtain ⟨_,_,γ,_,h0,h1,hmin⟩ :=
      (A j).metric.exists_minimizing_geodesic_of_metricComplete (A j).complete x y
    refine ⟨γ,h0,h1,?_⟩
    intro a ha b hb
    change ((A j).metric.edist (γ a) (γ b)).toReal =
      |a-b| *((A j).metric.edist x y).toReal
    rw [hmin a ha b hb,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]
  let (y : Y.carrier) : ProperSpace (Y.rebase y).carrier :=
    show ProperSpace Y.carrier from inferInstance
  have hrefBad (i : S) :
      Tendsto (fun j => badAscentRadius c b (incl j (ref j ⟨i.val,hSK i.property⟩)))
        atTop (𝓝 0) := by
    apply RiemannianMetric.tendsto_badAscentRadius_zero_of_pointedGHConvergesUnbounded
      g D (fun j => (A j).complete) (fun j => (A j).sectional_lower)
      (fun j => incl j (ref j ⟨i.val,hSK i.property⟩))
      (hvconv ⟨i.val,hSK i.property⟩) (R := 2*b) (by linarith) hplus
    intro y hy hyb
    exact hstrong i y hy hyb.le
  have hselect (i : S) := RiemannianMetric.exists_near_min_badAscentRadius_subset_centers_of_tendsto_zero
    g (fun j => (A j).complete) E (fun j => corner_boundedFiberSection_isCompact (A j))
    hc1 hb hρ (fun j => incl j (ref j ⟨i.val,hSK i.property⟩))
    (fun j => hrefE j ⟨i.val,hSK i.property⟩) (hrefBad i)
  choose q₀ hq₀ hqzero using hselect
  choose q hqrad hqeq using fun (i : S) (j : ℕ) => (hq₀ i j).1
  have hqdist (i : S) :
      Tendsto (fun j => ((A j).metric.edist
        (incl j (ref j ⟨i.val,hSK i.property⟩)) (incl j (q i j))).toReal)
        atTop (𝓝 0) := by
    have hz := tendsto_dist_zero_of_badAscentRadius_zero_at_scaled_spire_in_expanding_subset
      hXgeo hgeo (by norm_num : (0:ℝ) ≤ 3/2) E
      (fun j x hx => (A j).boundedFiberSection_dist_le x hx) hs ht hsTop htTop Q hQ
      (K : Set Y.carrier) K.isCompact hK hε hforward ⟨i.val,hSK i.property⟩
      (fun j => ⟨incl j (ref j ⟨i.val,hSK i.property⟩),hrefE j _⟩)
      (fun j => ⟨q₀ i j,(hq₀ i j).1⟩)
      (fun j => hmark ⟨i.val,hSK i.property⟩ j)
      (κ := 1/4) (by norm_num) hρ hb (by norm_num; linarith) hbcap
      (fun j => (hq₀ i j).2.1) hc hminus B hBmax
      (fun y hy hne => by
        have hi : i.val ∈ (S : Set Y.carrier) := i.property
        rw [hS] at hi
        simpa only [one_div_mul_eq_div] using hi.2 y hy hne)
      (hqzero i)
    change Tendsto (fun j => ((A j).metric.edist
      (incl j (ref j ⟨i.val,hSK i.property⟩)) (q₀ i j)).toReal) atTop (𝓝 0) at hz
    simpa only [← hqeq,incl] using hz
  let vl (j : ℕ) (y : K) :
      (ballModel (A j).basedSpace (s j) ((by norm_num : (0:ℝ)<3/2).trans (hs j))).carrier :=
    ⟨incl j (ref j y),Metric.mem_ball'.mpr ((href j y).trans_lt (hs j))⟩
  let vr (j : ℕ) (y : K) :
      (ballModel Y (t j) ((by norm_num : (0:ℝ)<3/2).trans (ht j))).carrier :=
    ⟨y.val,Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩
  have hmark' (j : ℕ) (y : K) : dist ((Q j).left (vl j y)) ((Q j).right (vr j y)) < ε j :=
    hmark y j
  have hpairlim (y z : K) :
      Tendsto (fun j => ((A j).metric.edist (incl j (ref j y)) (incl j (ref j z))).toReal)
        atTop (𝓝 (dist y.val z.val)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (g := fun j => ε j+ε j) (fun _ => dist_nonneg)
    · intro j
      have hd := dist_dist_dist_le ((Q j).left (vl j y)) ((Q j).left (vl j z))
        ((Q j).right (vr j y)) ((Q j).right (vr j z))
      rw [(Q j).left_isometry.dist_eq,(Q j).right_isometry.dist_eq] at hd
      exact hd.trans (add_le_add (hmark' j y).le (hmark' j z).le)
    · simpa only [add_zero] using hε.add hε
  let ql (j : ℕ) (i : S) :
      (ballModel (A j).basedSpace (s j) ((by norm_num : (0:ℝ)<3/2).trans (hs j))).carrier :=
    ⟨incl j (q i j),Metric.mem_ball'.mpr ((hqrad i j).trans_lt (hs j))⟩
  have hqconv (i : S) :
      PointedGHConvergesUnbounded
        (fun j => (A j).metric.toBasedMetricSpace (incl j (q i j))) (Y.rebase i.val) := by
    have hqCross : Tendsto (fun j =>
        dist ((Q j).left (ql j i)) ((Q j).right (vr j ⟨i.val,hSK i.property⟩)))
        atTop (𝓝 0) := by
      apply squeeze_zero (g := fun j => ((A j).metric.edist
        (incl j (ref j ⟨i.val,hSK i.property⟩)) (incl j (q i j))).toReal+ε j)
        (fun _ => dist_nonneg)
      · intro j
        have hd := dist_triangle ((Q j).left (ql j i))
          ((Q j).left (vl j ⟨i.val,hSK i.property⟩))
          ((Q j).right (vr j ⟨i.val,hSK i.property⟩))
        rw [(Q j).left_isometry.dist_eq] at hd
        change dist ((Q j).left (ql j i)) ((Q j).right (vr j ⟨i.val,hSK i.property⟩)) ≤
          dist (incl j (q i j)) (incl j (ref j ⟨i.val,hSK i.property⟩))+
            dist ((Q j).left (vl j ⟨i.val,hSK i.property⟩))
              ((Q j).right (vr j ⟨i.val,hSK i.property⟩)) at hd
        rw [dist_comm (incl j (q i j))] at hd
        exact hd.trans (add_le_add le_rfl (hmark' j ⟨i.val,hSK i.property⟩).le)
      · simpa only [add_zero] using (hqdist i).add hε
    exact pointedGHConvergesUnbounded_rebase_of_expanding_realizations
      hXgeo hgeo (fun j => (by norm_num : (0:ℝ)<3/2).trans (hs j))
      (fun j => (by norm_num : (0:ℝ)<3/2).trans (ht j))
      hsTop htTop Q hQ (fun j => ql j i) (fun j => vr j ⟨i.val,hSK i.property⟩)
      i.val (Filter.Eventually.of_forall fun _ => rfl) hqCross
  refine ⟨s,t,ε,hsTop,htTop,hεpos,hε,hs,ht,Q,hQ,hK,hforward,hback,
    B,P,S,b,ρ,hB,hBasc,hBmax,hPK,hSK,hS,hcover,hb,hbcap,hρ,hρb,hstrong,
    ref,fun j i => q i j,href,fun j y => hmark y j,hpairlim,
    fun y => ⟨hrad y,hvconv y⟩,fun j i => hqrad i j,?_,?_⟩
  · intro j i
    simpa only [← hqeq,incl] using (hq₀ i j).2
  · intro i
    refine ⟨hrefBad i,?_,hqdist i,hqconv i⟩
    simpa only [← hqeq,incl] using hqzero i

theorem PoincareConjecture.eventually_boundedFiberSection_subset_ball_cover_of_same_realizations
    {m k : ℕ} {δ H : ℝ} (A : ℕ → PointedCornerModel m k δ H)
    {Y : BasedMetricSpaceBundle.{0}} (K : Set Y.carrier)
    {s t ε : ℕ → ℝ} (hs : ∀ j, (3/2 : ℝ) < s j) (ht : ∀ j, (3/2 : ℝ) < t j)
    (hε : Tendsto ε atTop (𝓝 0))
    (Q : ∀ j, PointedGHRealization
      (ballModel (A j).basedSpace (s j) ((by norm_num : (0:ℝ)<3/2).trans (hs j)))
      (ballModel Y (t j) ((by norm_num : (0:ℝ)<3/2).trans (ht j))))
    (hK : K ⊆ Metric.closedBall Y.base (3/2))
    (hforward : ∀ j (x : (A j).boundedFiberSection), ∃ y : K,
      dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr
        (((A j).boundedFiberSection_dist_le x.val x.property).trans_lt (hs j))⟩)
        ((Q j).right ⟨y.val, Metric.mem_ball.mpr
          ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j)
    (ref : ∀ j, K → openFiber (A j).joint (A j).domain (A j).value)
    (href : ∀ j y, ((A j).metric.edist (A j).ambientPoint
      (openFiberIncl (A j).joint (A j).domain (A j).value (ref j y))).toReal ≤ 3/2)
    (hmark : ∀ j y,
      dist ((Q j).left ⟨openFiberIncl (A j).joint (A j).domain (A j).value (ref j y),
        Metric.mem_ball'.mpr ((href j y).trans_lt (hs j))⟩)
        ((Q j).right ⟨y.val, Metric.mem_ball.mpr
          ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j)
    {ι : Type*} (y : ι → K) (r : ι → ℝ)
    (hcover : (univ : Set K) ⊆ ⋃ i, Metric.ball (y i) (r i))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in atTop, letI := (A j).metric.toMetricSpace
      (A j).boundedFiberSection ⊆ ⋃ i, Metric.ball
        (openFiberIncl (A j).joint (A j).domain (A j).value (ref j (y i))) (r i+η) := by
  let (j : ℕ) : MetricSpace (A j).carrier := (A j).metric.toMetricSpace
  filter_upwards [hε.eventually_lt_const (half_pos hη)] with j hj
  intro x hx
  obtain ⟨z,hxz⟩ := hforward j ⟨x,hx⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover (mem_univ z))
  refine mem_iUnion.mpr ⟨i,Metric.mem_ball.mpr ?_⟩
  let x' : (ballModel (A j).basedSpace (s j)
      ((by norm_num : (0:ℝ)<3/2).trans (hs j))).carrier :=
    ⟨x,Metric.mem_ball'.mpr (((A j).boundedFiberSection_dist_le x hx).trans_lt (hs j))⟩
  let q' : (ballModel (A j).basedSpace (s j)
      ((by norm_num : (0:ℝ)<3/2).trans (hs j))).carrier :=
    ⟨openFiberIncl (A j).joint (A j).domain (A j).value (ref j (y i)),
      Metric.mem_ball'.mpr ((href j (y i)).trans_lt (hs j))⟩
  let z' : (ballModel Y (t j) ((by norm_num : (0:ℝ)<3/2).trans (ht j))).carrier :=
    ⟨z.val,Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hK z.property)).trans_lt (ht j))⟩
  let y' : (ballModel Y (t j) ((by norm_num : (0:ℝ)<3/2).trans (ht j))).carrier :=
    ⟨(y i).val,Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp (hK (y i).property)).trans_lt (ht j))⟩
  have hxz' : dist ((Q j).left x') ((Q j).right z') < ε j := hxz
  have hqy : dist ((Q j).left q') ((Q j).right y') < ε j := hmark j (y i)
  have hzy : dist ((Q j).right z') ((Q j).right y') < r i := by
    rw [(Q j).right_isometry.dist_eq]
    exact Metric.mem_ball.mp hi
  have htri := dist_triangle4 ((Q j).left x') ((Q j).right z')
    ((Q j).right y') ((Q j).left q')
  rw [dist_comm ((Q j).right y') ((Q j).left q'),(Q j).left_isometry.dist_eq] at htri
  change dist x' q' < r i+η
  linarith
