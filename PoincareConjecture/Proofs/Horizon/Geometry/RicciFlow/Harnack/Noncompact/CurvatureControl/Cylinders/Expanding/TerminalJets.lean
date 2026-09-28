import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Terminal.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Derivatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u
namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

private theorem exists_terminal_spatial_curvature_bounds
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M]
        (J : Set ℝ) (F : RicciFlow (m + 1) M J),
        Icc (-2 : ℝ) 0 ⊆ interior J →
        (∀ t ∈ Icc (-2 : ℝ) 0, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc (-2 : ℝ) 0, ∀ y : M,
          (F.connection t).NonnegativeCurvatureOperator y) →
        ∀ p : M,
        (∀ t ∈ Icc (-2 : ℝ) 0,
          ∀ y ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
            (F.connection t).scalarCurvature y ≤ 4) →
        ∀ j, ∀ t ∈ Icc (-1 : ℝ) 0, ∀ y : M,
          (F.metric 0).edist p y ≤ ENNReal.ofReal (16 * (((m + 1 : ℕ) : ℝ) + 8)) →
          (F.connection t).curvatureDerivativeNorm j y ≤ K j := by
  let n : ℝ := ((m + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  choose K hK hbound using fun j => exists_terminal_cylinder_derivative_constant hC hm j
    (S := 4) (A := 8 * n ^ 2) (r := 64 * (n + 8)) (scale := 1)
    (by norm_num) (by positivity) (by positivity) (by norm_num)
  refine ⟨K, fun j => (hK j).le, ?_⟩
  intro M _ _ _ _ _ J F hJ hcomplete hoperator p hscalar j t ht y hy
  have htime : (0 : ℝ) - (-2) ≤ (8 * n ^ 2) / (n ^ 2 * 4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    ring_nf
    rfl
  have hgap : 64 * (n + 8) / 4 + (4 * n * 1 + 8 * 4 / 1) * (0 - (-2)) <
      64 * (n + 8) / 2 := by linarith
  have hy' : (F.metric 0).edist p y ≤ ENNReal.ofReal (64 * (n + 8) / 4) := by
    convert hy using 1
    congr 1
    dsimp [n]
    ring
  have h := hbound j M J F (-2) 0 (by norm_num) hJ hcomplete hoperator p
    htime hgap hscalar t ⟨by linarith [ht.1], ht.2⟩ y hy'
  have hden : (1 : ℝ) ≤ (t - (-2)) ^ ((j : ℝ) / 2) :=
    Real.one_le_rpow (by linarith [ht.1]) (by positivity)
  exact h.trans ((div_le_iff₀ (zero_lt_one.trans_le hden)).mpr (by nlinarith [hK j]))

private theorem terminal_pullback_ellipticity
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u})
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M]
    {J : Set ℝ} (F : RicciFlow (m + 1) M J)
    (hJ : Icc (-2 : ℝ) 0 ⊆ J)
    (hoperator : ∀ t ∈ Icc (-2 : ℝ) 0, ∀ y : M,
      (F.connection t).NonnegativeCurvatureOperator y)
    (p : M)
    (hscalar : ∀ t ∈ Icc (-2 : ℝ) 0,
      ∀ y ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
        (F.connection t).scalarCurvature y ≤ 4)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (e : EuclideanSpace ℝ (Fin (m + 1)) → M) (x : EuclideanSpace ℝ (Fin (m + 1)))
    (hx : (F.metric 0).edist p (e x) ≤
      ENNReal.ofReal (16 * (((m + 1 : ℕ) : ℝ) + 8)))
    {a b : ℝ}
    (hinit : ∀ v, a * ‖v‖ ^ 2 ≤ (F.metric (-δ)).pullbackCoefficients e x v v ∧
      (F.metric (-δ)).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc (-δ) 0) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    (Real.exp (-8) * a) * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
      (F.metric t).pullbackCoefficients e x v v ≤ (Real.exp 8 * b) * ‖v‖ ^ 2 := by
  have hsub : Icc (-δ) 0 ⊆ Icc (-2 : ℝ) 0 := Icc_subset_Icc (by linarith) le_rfl
  have hxball : e x ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)) :=
    hx.trans_lt (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by
      have hdim : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
      linarith))
  let w := mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e x v
  have hn (s : ℝ) : 0 ≤ (F.metric s).inner (e x) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric s).pos _ _ hw).le
  have hRic (s : ℝ) (hs : s ∈ Icc (-δ) 0) :
      |(F.connection s).ricci (e x) w w| ≤ 4 * (F.metric s).inner (e x) w w := by
    have h := (F.connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric s) (F.connection s)) (e x)
      (hoperator s (hsub hs) (e x)) w
    rw [abs_of_nonneg h.1]
    exact h.2.trans (mul_le_mul_of_nonneg_right (hscalar s (hsub hs) (e x) hxball) (hn s))
  have hcomp := F.metric_inner_self_exp_bounds (convex_Icc (-δ) 0)
    (fun _ hs => hJ (hsub hs)) (e x) w 4 hRic ⟨le_rfl, by linarith⟩ ht
  have htime : |t - (-δ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hl : Real.exp (-8) ≤ Real.exp (-(2 * 4) * |t - (-δ)|) :=
    Real.exp_le_exp.mpr (by linarith)
  have hu : Real.exp ((2 * 4) * |t - (-δ)|) ≤ Real.exp 8 :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · calc
      _ = Real.exp (-8) * (a * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-8) * (F.metric (-δ)).inner (e x) w w :=
        mul_le_mul_of_nonneg_left (hinit v).1 (Real.exp_nonneg _)
      _ ≤ Real.exp (-(2 * 4) * |t - (-δ)|) * (F.metric (-δ)).inner (e x) w w :=
        mul_le_mul_of_nonneg_right hl (hn (-δ))
      _ ≤ _ := hcomp.1
  · calc
      _ ≤ Real.exp ((2 * 4) * |t - (-δ)|) * (F.metric (-δ)).inner (e x) w w := hcomp.2
      _ ≤ Real.exp 8 * (F.metric (-δ)).inner (e x) w w :=
        mul_le_mul_of_nonneg_right hu (hn (-δ))
      _ ≤ Real.exp 8 * (b * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hinit v).2 (Real.exp_nonneg _)
      _ = _ := by ring



theorem exists_terminal_cylinder_spatialJet_time_constant
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (d : ℕ) (Z : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M]
        (J : Set ℝ), IsOpen J → ∀ F : RicciFlow (m + 1) M J,
        Icc (-2 : ℝ) 0 ⊆ J →
        (∀ t ∈ Icc (-2 : ℝ) 0, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc (-2 : ℝ) 0, ∀ y : M,
          (F.connection t).NonnegativeCurvatureOperator y) →
        ∀ p : M,
        (∀ t ∈ Icc (-2 : ℝ) 0,
          ∀ y ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
            (F.connection t).scalarCurvature y ≤ 4) →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
        ∀ {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin (m + 1)) → M},
          ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U →
          (∀ y ∈ U, (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y).IsInvertible) →
        ∀ {x : EuclideanSpace ℝ (Fin (m + 1))}, x ∈ U →
        (F.metric 0).edist p (e x) ≤
          ENNReal.ofReal (16 * (((m + 1 : ℕ) : ℝ) + 8)) →
        (∀ v, a * ‖v‖ ^ 2 ≤ (F.metric (-δ)).pullbackCoefficients e x v v ∧
          (F.metric (-δ)).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j ≤ d,
          ‖iteratedFDeriv ℝ j ((F.metric (-δ)).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ j ≤ d, ∀ s ∈ Icc (-δ) 0, ∀ t ∈ Icc (-δ) 0,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ B * |t - s| := by
  obtain ⟨K, hK, hcurvature⟩ := exists_terminal_spatial_curvature_bounds hC hm
  obtain ⟨B, hB, htime⟩ := SpacetimeBounds.exists_spatialJet_time_lipschitz_constant
    (m + 1) d K Z hK (a := Real.exp (-8) * a) (b := Real.exp 8 * b)
    (by positivity) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ _ J hJ F hsub hcomplete hoperator p hscalar δ hδ hδone U hU e he hi x hx hdist hell hinit j hj s hs t ht
  have hsubδ : Icc (-δ) 0 ⊆ Icc (-2 : ℝ) 0 := Icc_subset_Icc (by linarith) le_rfl
  have hcurv := hcurvature M J F (by simpa only [hJ.interior_eq] using hsub)
    hcomplete hoperator p hscalar
  have h := htime F hJ hU he hi (fun _ hu => hsub (hsubδ hu))
    (by linarith : (0 : ℝ) - (-δ) ≤ 1) (show -δ ∈ Icc (-δ) 0 by constructor <;> linarith)
    hx (fun u hu v => terminal_pullback_ellipticity hC F hsub hoperator p hscalar
      hδ hδone e x hdist hell hu v)
    (fun k _ u hu => hcurv k u ⟨by linarith [hu.1], hu.2⟩ (e x) hdist) hinit
  exact (h j hj).2 s hs t ht




theorem eventually_terminal_spatialJet_control_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hopen : ∀ k, IsOpen (J k))
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ y : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator y)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ y ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature y ≤ 4)
    (d : ℕ) (Z : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ᶠ k in atTop,
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}, IsOpen U →
      ∀ {e : EuclideanSpace ℝ (Fin (m + 1)) → (C k).carrier},
        ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y).IsInvertible) →
      ∀ {x : EuclideanSpace ℝ (Fin (m + 1))}, x ∈ U →
      ((F k).metric 0).edist (p k) (e x) ≤ ENNReal.ofReal R →
      (∀ v, a * ‖v‖ ^ 2 ≤ ((F k).metric (-δ)).pullbackCoefficients e x v v ∧
        ((F k).metric (-δ)).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
      (∀ j ≤ d,
        ‖iteratedFDeriv ℝ j (((F k).metric (-δ)).pullbackCoefficients e) x‖ ≤ Z j) →
      ∀ j ≤ d,
        ‖iteratedFDeriv ℝ j (((F k).metric 0).pullbackCoefficients e) x -
          iteratedFDeriv ℝ j (((F k).metric (-δ)).pullbackCoefficients e) x‖ ≤ B * δ := by
  obtain ⟨B, hB, hbound⟩ := exists_terminal_cylinder_spatialJet_time_constant hC hm d Z ha hb
  refine ⟨B, hB, ?_⟩
  intro R hR
  let r : ℝ := 64 * (((m + 1 : ℕ) : ℝ) + 8)
  have hr : 0 < r := by dsimp [r]; positivity
  filter_upwards [hA.eventually_ge_atTop 2, hL.eventually_ge_atTop (R + r + 1)] with k hkA hkL
  intro δ hδ hδone U hU e he hi x hx hdist hell hinit j hj
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : (C k).carrier → Type _) :=
    ⟨((F k).metric 0).toRiemannianMetric⟩
  have hsub : Icc (-2 : ℝ) 0 ⊆ Icc (-A k) 0 := Icc_subset_Icc (by linarith) le_rfl
  have hlocal : ∀ t ∈ Icc (-2 : ℝ) 0, ∀ y ∈ ((F k).metric 0).ball (e x) r,
      ((F k).connection t).scalarCurvature y ≤ 4 := by
    intro t ht y hy
    apply hscalar k t (hsub ht) y
    have htri : ((F k).metric 0).edist (p k) y ≤
        ((F k).metric 0).edist (p k) (e x) + ((F k).metric 0).edist (e x) y :=
      Manifold.riemannianEDist_triangle
    have hsum : ((F k).metric 0).edist (p k) y ≤ ENNReal.ofReal (R + r) := by
      rw [ENNReal.ofReal_add hR hr.le]
      exact htri.trans (add_le_add hdist hy.le)
    have hgap : ENNReal.ofReal (R + r) < ENNReal.ofReal (R + r + 1) :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by linarith)
    exact (hsum.trans_lt hgap).trans_le (ENNReal.ofReal_le_ofReal hkL)
  have h := hbound (C k).carrier (J k) (hopen k) (F k)
    (fun _ ht => interior_subset (hJ k (hsub ht)))
    (fun t ht => hcomplete k t (hsub ht))
    (fun t ht => hoperator k t (hsub ht)) (e x) hlocal hδ hδone hU he hi hx
    (by change Manifold.riemannianEDist (𝓡 (m + 1)) (e x) (e x) ≤ _
        rw [Manifold.riemannianEDist_self]; exact bot_le) hell hinit j hj
    (-δ) ⟨le_rfl, by linarith⟩ 0 ⟨by linarith, le_rfl⟩
  simpa only [zero_sub, neg_neg, abs_of_pos hδ] using h

end PoincareConjecture.RicciFlow
