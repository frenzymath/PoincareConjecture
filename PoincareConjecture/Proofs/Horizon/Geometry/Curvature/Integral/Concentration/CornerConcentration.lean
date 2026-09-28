import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerCenters
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SubsetAnnularCover
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiberConcentration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.AnnularStability
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AscentRestriction








noncomputable section

open Set Filter Topology MeasureTheory Function
open PoincareConjecture Poincare.GromovHausdorff Poincare.CurvatureIntegral
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
private theorem corner_closedBall_near_section_subset
    {m k : ℕ} {δ H : ℝ} (A : PointedCornerModel m k δ H)
    (q : A.carrier) (hq : (A.metric.edist A.ambientPoint q).toReal ≤ 3/2)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1/4) :
    ∀ y, A.metric.edist q y ≤ ENNReal.ofReal R → y ∈ A.metric.ball A.ambientPoint 2 := by
  let : MetricSpace A.carrier := A.metric.toMetricSpace
  intro y hy
  have hyR := ENNReal.toReal_le_of_le_ofReal hR0 hy
  rw [← A.metric.toMetricSpace_ball,Metric.mem_ball,dist_comm]
  change dist A.ambientPoint q ≤ 3/2 at hq
  change dist q y ≤ R at hyR
  have htri := dist_triangle A.ambientPoint q y
  linarith

private theorem corner_error_integrableOn_double_ball
    {m k : ℕ} {δ H : ℝ} (A : PointedCornerModel m k δ H) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) A.joint_smooth A.domain A.regular A.value
    letI := isManifold_openFiber (m := m) A.joint_smooth A.domain A.regular A.value
    let gL := A.metric.openRegularFiberMetric A.joint_smooth A.domain A.regular A.value
    IntegrableOn A.error
      (openFiberIncl A.joint A.domain A.value ⁻¹' A.metric.ball A.ambientPoint 2) gL.volumeMeasure := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) A.joint_smooth A.domain A.regular A.value
  let := isManifold_openFiber (m := m) A.joint_smooth A.domain A.regular A.value
  apply (A.error_continuous.continuousOn.integrableOn_compact
    (A.metric.isCompact_openFiber_preimage_closedBall A.complete A.joint_smooth.continuous
      A.domain A.value A.ambientPoint 2 A.buffer)).mono_set
  intro x hx
  exact (show A.metric.edist A.ambientPoint (openFiberIncl A.joint A.domain A.value x) <
    ENNReal.ofReal 2 from hx).le
private theorem corner_pointedGH_subseq
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    (h : PointedGHConvergesUnbounded X Y) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    PointedGHConvergesUnbounded (fun j => X (φ j)) Y := by
  intro r hr
  obtain ⟨δ,hδ,hpos,⟨⟨C,hC⟩,hdist⟩⟩ := h r hr
  exact ⟨fun j => δ (φ j),hδ.comp hφ,fun j => hpos (φ j),
    ⟨C,fun j => hC (φ j)⟩,hdist.comp hφ⟩


set_option maxHeartbeats 2500000 in
theorem PoincareConjecture.exists_corner_scalar_concentration_of_annular_bound
    {m k : ℕ} (hm : 1 ≤ m) {δ H v r₀ C cminus c cplus : ℝ}
    (hv : 0 ≤ v) (hvminus : v < cminus) (hminus : cminus < c)
    (hplus : c < cplus) (hplus1 : cplus < 1)
    (hr₀ : 0 < r₀) (hC : 0 < C)
    (hannular : ∀ (A : PointedCornerModel (m+2) k δ H)
        (p : openFiber A.joint A.domain A.value),
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k))) =
          (m+2)+k) := ⟨finrank_euclideanSpace_fin⟩
      letI := openFiberChartedSpace (m := m+2) A.joint_smooth A.domain A.regular A.value
      letI := isManifold_openFiber (m := m+2) A.joint_smooth A.domain A.regular A.value
      let incl := openFiberIncl A.joint A.domain A.value
      let gL := A.metric.openRegularFiberMetric A.joint_smooth A.domain A.regular A.value
      letI := A.metric.toMetricSpace
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        (∀ y, A.metric.edist (incl p) y ≤ ENNReal.ofReal (4*r) → y ∈ A.domain) →
        (∀ y : A.carrier, r/2 < dist (incl p) y → dist (incl p) y < 3*r →
          HasLocalDistanceAscent v (incl p) y) →
        (∫ x in {x | (A.metric.edist (incl p) (incl x)).toReal ∈
            Icc (113*r/96) (19*r/16)}, max 0 (gL.leviCivitaData.scalarCurvature x)
              ∂gL.volumeMeasure) ≤
          C*(r^m + ∫ x in {x | (A.metric.edist (incl p) (incl x)).toReal ∈
            Icc (r/2) (3*r)}, A.error x ∂gL.volumeMeasure))
    (A : ℕ → PointedCornerModel (m+2) k δ H)
    (T : CompatiblePointedCompactSystem.{0})
    (K : TopologicalSpace.NonemptyCompacts T.completedLimit.carrier)
    (hlim : IsExpandingCornerLimit A T K)
    (hdiv : Tendsto (fun j => (A j).weightedRatio) atTop atTop) :
    let Y := T.completedLimit
    ∃ y : K, dist Y.base y.val ≤ 5/4 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (ref q : ∀ j, openFiber (A (φ j)).joint (A (φ j)).domain (A (φ j)).value)
        (b ρ : ℝ) (a : ℕ → ℝ),
      0 < b ∧ 0 < ρ ∧
      (∀ z : Y.carrier, 0 < dist y.val z → dist y.val z ≤ b →
        HasLocalDistanceAscent cplus y.val z) ∧
      Tendsto (fun j => ((A (φ j)).metric.edist (A (φ j)).ambientPoint
        (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (ref j))).toReal)
        atTop (𝓝 (dist Y.base y.val)) ∧
      PointedGHConvergesUnbounded
        (fun j => (A (φ j)).metric.toBasedMetricSpace
          (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (ref j)))
        (Y.rebase y.val) ∧
      Tendsto (fun j => ((A (φ j)).metric.edist
        (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (ref j))
        (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (q j))).toReal)
        atTop (𝓝 0) ∧
      (∀ j, letI := (A (φ j)).metric.toMetricSpace
        ∀ z ∈ (A (φ j)).boundedFiberSection,
          dist (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (ref j)) z ≤ ρ →
          badAscentRadius c b
            (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (q j)) ≤
              2*badAscentRadius c b z) ∧
      (∀ j, 0 < a j) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ j, letI := (A (φ j)).metric.toMetricSpace
        a j = badAscentRadius c b
          (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (q j))) ∧
      Tendsto (fun j => (A (φ j)).metric.openFiberWeightedAmbientBallRatio
        (A (φ j)).joint_smooth (A (φ j)).domain (A (φ j)).regular (A (φ j)).value
        (A (φ j)).error
        (openFiberIncl (A (φ j)).joint (A (φ j)).domain (A (φ j)).value (q j))
        (4*a j) (8*a j)) atTop atTop := by
  classical
  let Y := T.completedLimit
  let g := fun j => (A j).metric
  let D := fun j => (A j).connection
  let incl := fun j => openFiberIncl (A j).joint (A j).domain (A j).value
  let E := fun j => (A j).boundedFiberSection
  let (j : ℕ) : MetricSpace (A j).carrier := (A j).metric.toMetricSpace
  let : ProperSpace Y.carrier := hlim.1
  let : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  let cap := min r₀ (1/64)
  have hcap : 0 < cap := lt_min hr₀ (by norm_num)
  have hcap₀ : cap ≤ r₀ := min_le_left _ _
  have hcap64 : cap ≤ 1/64 := min_le_right _ _
  obtain ⟨s,t,ε,hsTop,htTop,hεpos,hε,hs,ht,Q,hQ,hK,hforward,hback,
    B,P,S,b,ρ,hB,hBasc,hBmax,hPK,hSK,hS,hpunct,hb,hbcap,hρ,hρb,hstrong,
    ref,q,href,hmark,hpair,hrefconv,hqrad,hqmin,hqzero⟩ :=
    exists_corner_spire_centers_of_expanding_limit A T K hlim (hv.trans hvminus.le)
      hminus hplus hplus1 hcap
  let P' : Finset K := P.subtype (· ∈ K)
  let S' : Finset K := S.subtype (· ∈ K)
  let si (i : S') : S := ⟨i.val.val,Finset.mem_subtype.mp i.property⟩
  let qs := fun j (i : S') => q j (si i)
  have hpunct' : (univ : Set K) \ (S' : Set K) ⊆
      ⋃ y ∈ P', Metric.ball y (B y.val/4) \ {y} := by
    intro x hx
    have hxS : x.val ∉ S := by
      intro h
      exact hx.2 (Finset.mem_subtype.mpr h)
    obtain ⟨y,hy,hxy,hne⟩ := mem_iUnion₂.mp (hpunct ⟨x.property,hxS⟩)
    let y' : K := ⟨y,hPK hy⟩
    refine mem_iUnion₂.mpr ⟨y',Finset.mem_subtype.mpr hy,hxy,?_⟩
    intro heq
    exact hne (congrArg Subtype.val (mem_singleton_iff.mp heq))
  have htransfer : ∀ {ι : Type} [Finite ι] (y : ι → K) (r : ι → ℝ),
      (univ : Set K) ⊆ ⋃ i, Metric.ball (y i) (r i) →
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
        E j ⊆ ⋃ i, Metric.ball (incl j (ref j (y i))) (r i+η) := by
    intro ι _ y r hcover η hη
    exact eventually_boundedFiberSection_subset_ball_cover_of_same_realizations
      A K hs ht hε Q hK hforward ref href hmark y r hcover hη
  have hqsDist (i : S') : Tendsto
      (fun j => dist (incl j (ref j i.val)) (incl j (qs j i))) atTop (𝓝 0) :=
    (hqzero (si i)).2.2.1
  obtain ⟨O,hO,hOcover,hEcover⟩ :=
    exists_finite_annuli_and_spire_cover_of_subset_transfer E
      (fun j y => incl j (ref j y)) hpair isCompact_univ htransfer P' S'
      (fun y => B y.val)
      (fun y _ => ⟨(hB y.val).1,by have hh := (hB y.val).2; linarith⟩)
      hpunct' (fun j i => incl j (qs j i)) hqsDist
      (fun _ => b/12) (fun _ => div_pos hb (by norm_num))
  let o := fun j (a : O) => ref j a.val.1
  let rad := fun a : O => a.val.2
  have hradPos (a : O) : 0 < rad a := (hO a.val a.property).2.1
  have hradCap (a : O) : rad a ≤ cap := by
    have hr := (hO a.val a.property).2.2.2
    have hBB := (hB a.val.1.val).2
    have hp := hradPos a
    dsimp [rad] at hp ⊢
    linarith
  let Sgood : Finset K := S'.filter (fun y => dist Y.base y.val ≤ 5/4)
  let gi (i : Sgood) : S' := ⟨i.val,(Finset.mem_filter.mp i.property).1⟩
  let qc := fun j (i : Sgood) => qs j (gi i)
  let a := fun j (i : Sgood) => badAscentRadius c b (incl j (qc j i))
  have ha (j : ℕ) (i : Sgood) : 0 ≤ a j i := badAscentRadius_nonneg _ _ _
  have hab (j : ℕ) (i : Sgood) : a j i ≤ b := badAscentRadius_le hb.le _
  have hqradlim (i : S') :
      Tendsto (fun j => dist (A j).ambientPoint (incl j (qs j i)))
        atTop (𝓝 (dist Y.base i.val.val)) := by
    apply (hrefconv i.val).1.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun j => dist_dist_dist_le_right (A j).ambientPoint
        (incl j (ref j i.val)) (incl j (qs j i))) (hqsDist i)
  have hfar : ∀ᶠ j in atTop, ∀ i : S', ¬ dist Y.base i.val.val ≤ 5/4 →
      9/8 < dist (A j).ambientPoint (incl j (qs j i)) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : dist Y.base i.val.val ≤ 5/4
    · exact Filter.Eventually.of_forall fun j h => (h hi).elim
    · filter_upwards [(hqradlim i).eventually_const_lt (show 9/8 < dist Y.base i.val.val by linarith)]
        with j hj
      exact fun _ => hj
  have hcover : ∀ᶠ j in atTop,
      incl j ⁻¹' (A j).metric.ball (A j).ambientPoint 1 ⊆
        (⋃ i : O, {x | ((A j).metric.edist (incl j (o j i)) (incl j x)).toReal ∈
          Icc (113*rad i/96) (19*rad i/16)}) ∪
        ⋃ i : Sgood, incl j ⁻¹' (A j).metric.ball (incl j (qc j i)) (b/12) := by
    filter_upwards [hEcover,hfar] with j hj hfj
    intro x hx
    have hx1 : dist (A j).ambientPoint (incl j x) < 1 := by
      change incl j x ∈ (A j).metric.ball (A j).ambientPoint 1 at hx
      rw [← (A j).metric.toMetricSpace_ball] at hx
      exact Metric.mem_ball'.mp hx
    have hxE : incl j x ∈ E j := ⟨x,by change dist (A j).ambientPoint (incl j x) ≤ (3/2:ℝ); linarith only [hx1],rfl⟩
    rcases hj hxE with hord | hcrit
    · obtain ⟨z,hz,hlo,hhi⟩ := mem_iUnion₂.mp hord
      apply Or.inl
      refine mem_iUnion.mpr ⟨⟨z,hz⟩,?_,?_⟩
      · change 113*z.2/96 ≤ dist (incl j (ref j z.1)) (incl j x)
        convert hlo using 1
        ring
      · change dist (incl j (ref j z.1)) (incl j x) ≤ 19*z.2/16
        convert hhi using 1
        ring
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hcrit
      have hgood : dist Y.base i.val.val ≤ 5/4 := by
        by_contra hn
        have hfar' := hfj i hn
        have hxi : dist (incl j x) (incl j (qs j i)) < b/12 := Metric.mem_ball.mp hi
        have htri := dist_triangle (A j).ambientPoint (incl j x) (incl j (qs j i))
        linarith
      let i' : Sgood := ⟨i.val,Finset.mem_filter.mpr ⟨i.property,hgood⟩⟩
      apply Or.inr
      refine mem_iUnion.mpr ⟨i',?_⟩
      change incl j x ∈ (A j).metric.ball (incl j (qc j i')) (b/12)
      rw [← (A j).metric.toMetricSpace_ball]
      exact hi
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k))) = (m+2)+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let (j : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin (m+2)))
      (openFiber (A j).joint (A j).domain (A j).value) :=
    openFiberChartedSpace (m := m+2) (A j).joint_smooth (A j).domain (A j).regular (A j).value
  let (j : ℕ) : IsManifold (𝓡 (m+2)) ∞
      (openFiber (A j).joint (A j).domain (A j).value) :=
    isManifold_openFiber (m := m+2) (A j).joint_smooth (A j).domain (A j).regular (A j).value
  let gL := fun j => (A j).metric.openRegularFiberMetric
    (A j).joint_smooth (A j).domain (A j).regular (A j).value
  let DL := fun j => (gL j).leviCivitaData
  let W := fun j => incl j ⁻¹' (A j).metric.ball (A j).ambientPoint 2
  have hdomain (j : ℕ) (z : (A j).carrier)
      (hz : ((A j).metric.edist (A j).ambientPoint z).toReal ≤ 3/2)
      {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1/4) :
      ∀ y, (A j).metric.edist z y ≤ ENNReal.ofReal R → y ∈ (A j).domain := by
    intro y hy
    exact (A j).buffer y (show (A j).metric.edist (A j).ambientPoint y ≤
      ENNReal.ofReal 2 from (corner_closedBall_near_section_subset (A j) z hz hR0 hR y hy).le)
  have hWnear (j : ℕ) (z : (A j).carrier)
      (hz : ((A j).metric.edist (A j).ambientPoint z).toReal ≤ 3/2)
      {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1/4)
      (x : openFiber (A j).joint (A j).domain (A j).value)
      (hx : ((A j).metric.edist z (incl j x)).toReal ≤ R) : x ∈ W j := by
    apply corner_closedBall_near_section_subset (A j) z hz hR0 hR (incl j x)
    rw [← ENNReal.ofReal_toReal ((A j).metric.edist_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hx
  have hOrdAscent : ∀ᶠ j in atTop, ∀ i : O, ∀ y : (A j).carrier,
      rad i/2 < dist (incl j (o j i)) y → dist (incl j (o j i)) y < 3*rad i →
      HasLocalDistanceAscent v (incl j (o j i)) y := by
    apply eventually_all.mpr
    intro i
    let : ProperSpace (Y.rebase i.val.1.val).carrier := show ProperSpace Y.carrier from inferInstance
    have hh := RiemannianMetric.eventually_annular_distance_ascent_of_pointedGHConvergesUnbounded
      g D (fun j => (A j).complete) (K := 1) (by norm_num)
      (fun j => (A j).sectional_lower) (fun j => incl j (o j i))
      (hrefconv i.val.1).2 (half_pos (hradPos i)) hvminus
      (R := 3*rad i) (fun y hy hyR => hBasc i.val.1.val y
        ((half_pos (hradPos i)).trans_le hy)
        (hyR.trans_lt (hO i.val i.property).2.2.2))
    filter_upwards [hh] with j hj
    exact fun y hy hyR => hj y hy.le hyR.le
  have hCritAscent (j : ℕ) (i : Sgood) (r : ℝ) (hr : 0 < r)
      (har : 2*a j i ≤ r) (hrb : r ≤ b/6) :
      ∀ y : (A j).carrier, r/2 < dist (incl j (qc j i)) y →
        dist (incl j (qc j i)) y < 3*r →
        HasLocalDistanceAscent v (incl j (qc j i)) y := by
    intro y hy hyR
    have hh := hasLocalDistanceAscent_of_badAscentRadius_lt (c := c) (b := b)
      (p := incl j (qc j i)) (by dsimp only [a] at har; linarith)
      (by linarith)
    exact hh.mono (hvminus.trans hminus).le
  have hest : ∀ᶠ j in atTop,
      (∀ i : O,
        (∫ x in {x | ((A j).metric.edist (incl j (o j i)) (incl j x)).toReal ∈
          Icc (113*rad i/96) (19*rad i/16)}, max 0 ((DL j).scalarCurvature x)
          ∂(gL j).volumeMeasure) ≤
          C*(rad i)^m+C*∫ x in {x | ((A j).metric.edist (incl j (o j i)) (incl j x)).toReal ∈
            Icc (rad i/2) (3*rad i)}, (A j).error x ∂(gL j).volumeMeasure) ∧
      (∀ (i : Sgood) r, 0 < r → 2*a j i ≤ r → r ≤ b/6 →
        (∫ x in {x | ((A j).metric.edist (incl j (qc j i)) (incl j x)).toReal ∈
          Icc (113*r/96) (19*r/16)}, max 0 ((DL j).scalarCurvature x)
          ∂(gL j).volumeMeasure) ≤
          C*(r^m+∫ x in {x | ((A j).metric.edist (incl j (qc j i)) (incl j x)).toReal ∈
            Icc (r/2) (3*r)}, (A j).error x ∂(gL j).volumeMeasure)) := by
    filter_upwards [hOrdAscent] with j hj
    constructor
    · intro i
      have hp := hradPos i
      have hc := hradCap i
      have hh := hannular (A j) (o j i) (rad i) hp (hc.trans hcap₀)
        (hdomain j _ (href j i.val.1) (by positivity) (by linarith))
        (hj i)
      simpa only [mul_add] using hh
    · intro i r hr har hrb
      have hh := hannular (A j) (qc j i) r hr (by linarith)
        (hdomain j _ (hqrad j (si (gi i))) (by positivity) (by linarith))
        (hCritAscent j i r hr har hrb)
      exact hh
  have hWmeas (j : ℕ) : MeasurableSet (W j) := by
    change MeasurableSet (incl j ⁻¹' (A j).metric.ball (A j).ambientPoint 2)
    rw [← (A j).metric.toMetricSpace_ball]
    exact (Metric.isOpen_ball.preimage
      (isEmbedding_openFiberIncl (A j).joint (A j).domain (A j).value).continuous).measurableSet
  have hOrdBall (j : ℕ) (i : O) :
      ∀ y, (g j).edist (incl j (o j i)) y ≤ ENNReal.ofReal (3*rad i) →
        y ∈ (A j).domain := by
    have hp := hradPos i
    have hh := hradCap i
    exact hdomain j _ (href j i.val.1) (by positivity) (by linarith)
  have hCritBall (j : ℕ) (i : Sgood) :
      ∀ y, (g j).edist (incl j (qc j i)) y ≤ ENNReal.ofReal (3*(b/6)) →
        y ∈ (A j).domain :=
    hdomain j _ (hqrad j (si (gi i))) (by positivity) (by linarith)
  have hDoubleBall (j : ℕ) (i : Sgood) :
      ∀ y, (g j).edist (incl j (qc j i)) y ≤ ENNReal.ofReal (8*a j i) →
        y ∈ (A j).domain := by
    have h0 := ha j i
    have h1 := hab j i
    exact hdomain j _ (hqrad j (si (gi i))) (by positivity) (by linarith)
  have hOrdBuffer (j : ℕ) (i : O) :
      {x | ((g j).edist (incl j (o j i)) (incl j x)).toReal ∈
        Icc (rad i/2) (3*rad i)} ⊆ W j := by
    intro x hx
    have hp := hradPos i
    have hh := hradCap i
    exact hWnear j _ (href j i.val.1) (by positivity) (by linarith) x hx.2
  have hCritBuffer (j : ℕ) (i : Sgood) :
      {x | ((g j).edist (incl j (qc j i)) (incl j x)).toReal ≤ 3*(b/6)} ⊆ W j :=
    fun x hx => hWnear j _ (hqrad j (si (gi i))) (by positivity) (by linarith) x hx
  have hDoubleBuffer (j : ℕ) (i : Sgood) :
      incl j ⁻¹' (g j).ball (incl j (qc j i)) (8*a j i) ⊆ W j := by
    intro x hx
    have h0 := ha j i
    have h1 := hab j i
    apply hWnear j _ (hqrad j (si (gi i))) (show 0 ≤ 8*a j i by positivity)
      (show 8*a j i ≤ 1/4 by linarith) x
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (show (g j).edist (incl j (qc j i)) (incl j x) < ENNReal.ofReal (8*a j i) from hx).le
  obtain ⟨i,φ,hφ,hapos,hposdiv,_⟩ :=
    RiemannianMetric.exists_subseq_openFiber_critical_ambient_ball_weighted_scalar_integral_tendsto_atTop
      g (fun j => (A j).complete) (fun j => (A j).joint)
      (fun j => (A j).joint_smooth) (fun j => (A j).domain)
      (fun j => (A j).regular) (fun j => (A j).value) (by omega) hm
      DL (fun j => (A j).point) o rad (fun i => C*(rad i)^m) (fun _ => C)
      qc a (fun _ => b/6) (fun _ => b/12) (fun _ => C) W (fun j => (A j).error)
      (fun j => (A j).error_sectional_lower) hWmeas
      (fun j => corner_error_integrableOn_double_ball (A j))
      (fun j => (A j).error_nonneg) ha
      (fun _ => by positivity) (fun _ => by positivity) (fun _ => by linarith)
      (fun _ => hC.le) (fun _ => hC.le) (fun i => (hradPos i).le)
      (fun j y hy => (A j).buffer y (hy.trans (ENNReal.ofReal_le_ofReal (by norm_num))))
      hOrdBall hCritBall hDoubleBall hOrdBuffer hCritBuffer hDoubleBuffer
      (hcover.and hest) hdiv
  refine ⟨i.val,(Finset.mem_filter.mp i.property).2,φ,hφ,
    (fun j => ref (φ j) i.val),(fun j => qc (φ j) i),b,ρ,
    (fun j => a (φ j) i),hb,hρ,?_,?_,?_,?_,?_,hapos,?_,?_,?_⟩
  · intro z hz hzb
    exact hstrong (si (gi i)) z hz (by linarith)
  · exact (hrefconv i.val).1.comp hφ.tendsto_atTop
  · exact corner_pointedGH_subseq (hrefconv i.val).2 φ hφ.tendsto_atTop
  · exact (hqzero (si (gi i))).2.2.1.comp hφ.tendsto_atTop
  · intro j
    exact (hqmin (φ j) (si (gi i))).2.2
  · exact (hqzero (si (gi i))).2.1.comp hφ.tendsto_atTop
  · exact fun _ => rfl
  · exact hposdiv
