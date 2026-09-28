import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerRescaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.ExpandingSubsetRankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.RiemannianLimit









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory Function
open Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture

private theorem corner_pointedGHConvergesUnbounded_comp
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    (h : PointedGHConvergesUnbounded X Y) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    PointedGHConvergesUnbounded (fun j => X (φ j)) Y := by
  intro r hr
  obtain ⟨δ, hδ, hpos, ⟨⟨C, hC⟩, hdist⟩⟩ := h r hr
  exact ⟨fun j => δ (φ j), hδ.comp hφ, fun j => hpos (φ j),
    ⟨C, fun j => hC (φ j)⟩, hdist.comp hφ⟩

private theorem cornerModel_geodesic
    {m k : ℕ} {δ H : ℝ} (A : PointedCornerModel m k δ H)
    (x y : A.basedSpace.carrier) :
    ∃ γ : ℝ → A.basedSpace.carrier, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s-t| * dist x y := by
  obtain ⟨_, _, γ, _, h0, h1, hmin⟩ :=
    A.metric.exists_minimizing_geodesic_of_metricComplete A.complete x y
  refine ⟨γ, h0, h1, ?_⟩
  intro s hs t ht
  change (A.metric.edist (γ s) (γ t)).toReal = |s-t| * (A.metric.edist x y).toReal
  rw [hmin s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]


private theorem exists_small_rescaled_cornerModel
    {m k : ℕ} {δ H : ℝ} (hm : 2 ≤ m) (hH : 0 ≤ H)
    (A : PointedCornerModel m k δ H) (q : openFiber A.joint A.domain A.value)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/64)
    (hq : (A.metric.edist A.ambientPoint
      (openFiberIncl A.joint A.domain A.value q)).toReal < 4/3) :
    ∃ B : PointedCornerModel m k δ H, ∃ F : A.carrier ≃ B.carrier,
      F (openFiberIncl A.joint A.domain A.value q) = B.ambientPoint ∧
      (∀ x y, (A.metric.edist x y).toReal =
        (4*r)*(B.metric.edist (F x) (F y)).toReal) ∧
      (∀ z ∈ B.boundedFiberSection, F.symm z ∈ A.boundedFiberSection) ∧
      A.metric.openFiberWeightedAmbientBallRatio A.joint_smooth A.domain A.regular
        A.value A.error (openFiberIncl A.joint A.domain A.value q) (4*r) (8*r) ≤
          B.weightedRatio := by
  classical
  let : MetricSpace A.carrier := A.metric.toMetricSpace
  let scaleFactor : ℝ := ((4*r)^2)⁻¹
  have hr4 : 0 < 4*r := by positivity
  have hscaleFactor : 1 ≤ scaleFactor := by
    apply (one_le_inv₀ (sq_pos_of_pos hr4)).mpr
    nlinarith
  have hsqrt : Real.sqrt scaleFactor = (4*r)⁻¹ := by
    dsimp [scaleFactor]
    rw [Real.sqrt_inv, Real.sqrt_sq hr4.le]
  have h1 : 1 / Real.sqrt scaleFactor = 4*r := by rw [hsqrt, one_div, inv_inv]
  have h2 : 2 / Real.sqrt scaleFactor = 8*r := by rw [hsqrt, div_inv_eq_mul]; ring
  have hbuf : ∀ z : A.carrier,
      A.metric.edist (openFiberIncl A.joint A.domain A.value q) z ≤
        ENNReal.ofReal (2 / Real.sqrt scaleFactor) → z ∈ A.domain := by
    intro z hz
    apply A.buffer z
    rw [h2] at hz
    have hz' : dist (openFiberIncl A.joint A.domain A.value q) z ≤ 8*r := by
      exact (ENNReal.toReal_le_toReal (A.metric.edist_ne_top _ _) ENNReal.ofReal_ne_top).mpr hz
        |>.trans_eq (ENNReal.toReal_ofReal (by positivity))
    have hpz : dist A.ambientPoint z ≤ 2 := by
      have ht := dist_triangle A.ambientPoint
        (openFiberIncl A.joint A.domain A.value q) z
      change dist A.ambientPoint (openFiberIncl A.joint A.domain A.value q) < 4/3 at hq
      linarith
    exact (ENNReal.toReal_le_toReal (A.metric.edist_ne_top _ _) ENNReal.ofReal_ne_top).mp
      (by simpa [PointedCornerModel.ambientPoint] using hpz)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) A.joint_smooth A.domain A.regular A.value
  let := isManifold_openFiber (m := m) A.joint_smooth A.domain A.regular A.value
  obtain ⟨B, eM, eL, hmetric, hdist, hpoint, hf, hh, hvalue, hdomain,
    hinc, hqpoint, herror, hratio⟩ := exists_rescaled_pointedCornerModel hm hH A q hscaleFactor hbuf
  let : MetricSpace B.carrier := B.metric.toMetricSpace
  let := openFiberChartedSpace (m := m) B.joint_smooth B.domain B.regular B.value
  let := isManifold_openFiber (m := m) B.joint_smooth B.domain B.regular B.value
  have hscale (x y : A.carrier) :
      (A.metric.edist x y).toReal = (4*r)*(B.metric.edist (eM x) (eM y)).toReal := by
    have he := congrArg ENNReal.toReal (hdist x y)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsqrt] at he
    rw [he, ← mul_assoc, mul_inv_cancel₀ hr4.ne', one_mul]
  refine ⟨B, eM.toEquiv, hpoint.symm, hscale, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    let v := eL.symm w
    have hincv : eM (openFiberIncl A.joint A.domain A.value v) =
        openFiberIncl B.joint B.domain B.value w := by
      rw [← hinc, eL.apply_symm_apply]
    have hinv : eM.symm (openFiberIncl B.joint B.domain B.value w) =
        openFiberIncl A.joint A.domain A.value v := by rw [← hincv, eM.symm_apply_apply]
    refine ⟨v, ?_, hinv.symm⟩
    have hqw := hscale (openFiberIncl A.joint A.domain A.value q)
      (openFiberIncl A.joint A.domain A.value v)
    rw [← hpoint, hincv] at hqw
    have ht := dist_triangle A.ambientPoint
      (openFiberIncl A.joint A.domain A.value q) (openFiberIncl A.joint A.domain A.value v)
    change dist A.ambientPoint (openFiberIncl A.joint A.domain A.value q) < 4/3 at hq
    change dist B.ambientPoint (openFiberIncl B.joint B.domain B.value w) ≤ 3/2 at hw
    change dist (openFiberIncl A.joint A.domain A.value q)
      (openFiberIncl A.joint A.domain A.value v) =
      (4*r)*dist B.ambientPoint (openFiberIncl B.joint B.domain B.value w) at hqw
    change dist A.ambientPoint (openFiberIncl A.joint A.domain A.value v) ≤ 3/2
    nlinarith
  · simpa only [h1,h2] using hratio



theorem exists_corner_limit_with_strictly_larger_rank
    {m k : ℕ} {δ H : ℝ} (hm : 2 ≤ m) (hH : 0 ≤ H)
    (A : ℕ → PointedCornerModel m k δ H)
    (S : CompatiblePointedCompactSystem.{0})
    (K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier)
    (hlim : IsExpandingCornerLimit A S K)
    (hdiv : Tendsto (fun j => (A j).weightedRatio) atTop atTop)
    (y : K) (hy : dist S.completedLimit.base y.val ≤ (5/4 : ℝ))
    (ref q : ∀ j, openFiber (A j).joint (A j).domain (A j).value)
    (href : Tendsto (fun j => ((A j).metric.edist (A j).ambientPoint
      (openFiberIncl (A j).joint (A j).domain (A j).value (ref j))).toReal)
      atTop (𝓝 (dist S.completedLimit.base y.val)))
    (hconvref : PointedGHConvergesUnbounded
      (fun j => (A j).metric.toBasedMetricSpace
        (openFiberIncl (A j).joint (A j).domain (A j).value (ref j)))
      (S.completedLimit.rebase y.val))
    (hrefq : Tendsto (fun j => ((A j).metric.edist
      (openFiberIncl (A j).joint (A j).domain (A j).value (ref j))
      (openFiberIncl (A j).joint (A j).domain (A j).value (q j))).toReal) atTop (𝓝 0))
    {θ c cplus b ρ : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi/2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2*θ))
    (hplus : c < cplus) (hb : 0 < b) (hρ : 0 < ρ)
    (hascent : ∀ z : S.completedLimit.carrier,
      0 < dist y.val z → dist y.val z ≤ b → HasLocalDistanceAscent cplus y.val z)
    (hqmin : ∀ j, letI := (A j).metric.toMetricSpace
      ∀ z ∈ (A j).boundedFiberSection,
        dist (openFiberIncl (A j).joint (A j).domain (A j).value (ref j)) z ≤ ρ →
        badAscentRadius c b
          (openFiberIncl (A j).joint (A j).domain (A j).value (q j)) ≤
            2*badAscentRadius c b z)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (hazero : Tendsto a atTop (𝓝 0))
    (hactual : ∀ j, a j = (letI := (A j).metric.toMetricSpace
      badAscentRadius c b (openFiberIncl (A j).joint (A j).domain (A j).value (q j))))
    (hcritical : Tendsto (fun j =>
      (A j).metric.openFiberWeightedAmbientBallRatio (A j).joint_smooth
        (A j).domain (A j).regular (A j).value (A j).error
        (openFiberIncl (A j).joint (A j).domain (A j).value (q j))
        (4*a j) (8*a j)) atTop atTop) :
    ∃ A' : ℕ → PointedCornerModel m k δ H,
    ∃ S' : CompatiblePointedCompactSystem.{0},
    ∃ K' : TopologicalSpace.NonemptyCompacts S'.completedLimit.carrier,
      IsExpandingCornerLimit A' S' K' ∧
      Tendsto (fun j => (A' j).weightedRatio) atTop atTop ∧
      minLocalAnglePackingRankOn θ (K : Set S.completedLimit.carrier) <
        minLocalAnglePackingRankOn θ (K' : Set S'.completedLimit.carrier) := by
  classical
  let incl := fun j => openFiberIncl (A j).joint (A j).domain (A j).value
  let (j : ℕ) : MetricSpace (A j).carrier := (A j).metric.toMetricSpace
  have hgood : ∀ᶠ j in atTop, a j ≤ 1/64 ∧
      dist (A j).ambientPoint (incl j (q j)) < 4/3 := by
    have hsum := href.add hrefq
    have hroom : dist S.completedLimit.base y.val + 0 < (4/3 : ℝ) := by linarith
    filter_upwards [hazero.eventually_lt_const (by norm_num : (0:ℝ)<1/64),
      hsum.eventually_lt_const hroom] with j hj hk
    refine ⟨hj.le, ?_⟩
    exact (dist_triangle (A j).ambientPoint (incl j (ref j)) (incl j (q j))).trans_lt hk
  obtain ⟨J,hJ⟩ := eventually_atTop.1 hgood
  let shift := fun j : ℕ => j+J
  have hshift : StrictMono shift := by intro i j hij; dsimp [shift]; omega
  have hbuild (j : ℕ) := exists_small_rescaled_cornerModel hm hH (A (shift j))
    (q (shift j)) (ha (shift j)) (hJ (shift j) (by dsimp [shift]; omega)).1
      (hJ (shift j) (by dsimp [shift]; omega)).2
  choose B F hcenter hscale hsection hratio using hbuild
  have hdivB : Tendsto (fun j => (B j).weightedRatio) atTop atTop :=
    tendsto_atTop_mono hratio (hcritical.comp hshift.tendsto_atTop)
  obtain ⟨φ,hφ,T,L,hnew⟩ := exists_subseq_expandingCornerLimit (by omega : 1 ≤ m+k) B
  let ξ := fun j => shift (φ j)
  have hξ : StrictMono ξ := hshift.comp hφ
  let : ProperSpace S.completedLimit.carrier := hlim.1
  let : ProperSpace (S.completedLimit.rebase y.val).carrier := hlim.1
  let : ProperSpace T.completedLimit.carrier := hnew.1
  let Z := fun j => (B (φ j)).basedSpace
  let (j : ℕ) : ProperSpace (Z j).carrier :=
    (B (φ j)).metric.properSpace_toMetricSpace (B (φ j)).complete
  obtain ⟨s,t,ε,hsTop,htTop,hεpos,hεzero,hs,ht,Q,hQ,hL,hbaseL,hforward,hback⟩ := hnew.2.2.2
  obtain ⟨N,hN⟩ :=
    RiemannianMetric.exists_comparisonAngle_packing_bound_of_sectional_pointed_limit.{0}
      (m+k) hθ
  have hpackOld := hN (fun j => (A j).metric) (fun j => (A j).ambientPoint)
    (fun j => (A j).connection) (fun j => (A j).complete)
    (fun j => (A j).sectional_lower) hlim.2.2.1
  have hpackNew := hN (fun j => (B (φ j)).metric) (fun j => (B (φ j)).ambientPoint)
    (fun j => (B (φ j)).connection) (fun j => (B (φ j)).complete)
    (fun j => (B (φ j)).sectional_lower) hnew.2.2.1
  refine ⟨(fun j => B (φ j)),T,L,hnew,hdivB.comp hφ.tendsto_atTop,?_⟩
  apply RiemannianMetric.minLocalAnglePackingRankOn_lt_of_expanding_subset_near_min_badAscentRadius
    (V := S.completedLimit.rebase y.val) (Y := T.completedLimit)
    (fun j => (A (ξ j)).metric) (fun j => (A (ξ j)).connection)
    (fun j => (A (ξ j)).complete) (fun j => (A (ξ j)).sectional_lower)
    (fun j => incl (ξ j) (ref (ξ j))) (fun j => incl (ξ j) (q (ξ j)))
    (corner_pointedGHConvergesUnbounded_comp hconvref ξ hξ.tendsto_atTop)
    hθ hθpi hc hcθ hplus hb hρ hascent (hrefq.comp hξ.tendsto_atTop)
    (fun j => (A (ξ j)).boundedFiberSection) (fun j => hqmin (ξ j))
    4 (by norm_num) (fun j => 4*a (ξ j)) (fun j => mul_pos (by norm_num) (ha (ξ j)))
    (by simpa only [Function.comp_def, mul_zero] using
      (tendsto_const_nhds.mul (hazero.comp hξ.tendsto_atTop)))
    (fun j => by rw [hactual])
    (fun j => F (φ j)) (fun j => hcenter (φ j)) (fun j => hscale (φ j))
    (fun j => cornerModel_geodesic (B (φ j))) hnew.2.1
    (by norm_num : (0:ℝ)≤3/2)
    (fun j => (by norm_num : (0:ℝ)<3/2).trans (hs j)) ht hsTop htTop Q hQ
    (L : Set T.completedLimit.carrier) L.nonempty hL hεzero ?_
    (K : Set S.completedLimit.carrier) y.property hpackOld hpackNew
  intro j z
  obtain ⟨x,hx⟩ := hback j z
  refine ⟨⟨x.val, Metric.mem_ball'.mpr
    (((B (φ j)).boundedFiberSection_dist_le x.val x.property).trans_lt (hs j))⟩,
      hsection (φ j) x.val x.property, ?_⟩
  exact hx


end PoincareConjecture
