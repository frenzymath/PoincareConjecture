import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.BallCover
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Summation

open Set MeasureTheory PoincareConjecture
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.RiemannianMetric.integral_le_uniform_ambient_cover_bound
    {n : ℕ} {M X : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace X] [Nonempty X]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hn : 1≤n)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1≤D.sectionalCurvature x v w)
    (p : M) (f : X → M) (hf : Measurable f) (hinside : ∀ x, f x∈g.ball p 2)
    (μ : Measure X) (R K : X → ℝ) (hRi : Integrable R μ) (hKi : Integrable K μ)
    (hRn : ∀ x, 0≤R x) (hKn : ∀ x, 0≤K x)
    {r B : ℝ} (hr : 0<r) (hr1 : r≤1) (hB : 0≤B)
    (hbound : ∀ x:X, (∫ y in f ⁻¹' g.ball (f x) r, R y ∂μ) ≤
      B*(1+∫ y in f ⁻¹' g.ball (f x) (2*r), K y ∂μ)) :
    (∫ x, R x ∂μ) ≤
      (⌈RiemannianMetric.modelVolume n 1 6 /
        RiemannianMetric.modelVolume n 1 (r/4)⌉₊:ℝ)*B*(1+∫ x, K x ∂μ) := by
  classical
  let : ConnectedSpace M := {toNonempty := ⟨p⟩}
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  let : SecondCountableTopology M := g.secondCountableTopology
  have hcompact : IsCompact (closure (g.ball p (5*2))) := by
    rw [←g.toMetricSpace_ball]
    exact (isCompact_closedBall p (5*2)).of_isClosed_subset
      isClosed_closure Metric.closure_ball_subset_closedBall
  obtain ⟨S,hS,hcard,_,hcover⟩ := g.exists_finset_cover_of_precompact_ball p hn
    (by norm_num : (0:ℝ)<2) (by positivity : 0<r/2) (by linarith : r/2≤2)
    (by norm_num : (0:ℝ)≤1) hcompact D
    (fun x _ v => D.ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound x 1 (hsec x) v)
  have hcenters (q : S) : ∃ x:X, ∀ y:X,
      f y∈g.ball q.val (r/2) → f y∈g.ball (f x) r := by
    by_cases hx : ∃ x:X, f x∈g.ball q.val (r/2)
    · obtain ⟨x,hx⟩ := hx
      refine ⟨x,?_⟩
      intro y hy
      rw [←g.toMetricSpace_ball] at hx hy ⊢
      change dist (f y) (f x)<r
      change dist (f x) q.val<r/2 at hx
      change dist (f y) q.val<r/2 at hy
      have ht := dist_triangle (f y) q.val (f x)
      rw [dist_comm q.val (f x)] at ht
      exact lt_of_le_of_lt ht (by linarith)
    · exact ⟨Classical.arbitrary X,fun y hy => (hx ⟨y,hy⟩).elim⟩
  choose center hcenter using hcenters
  have hmeas (x:X) (s:ℝ) : MeasurableSet (f ⁻¹' g.ball (f x) s) := by
    rw [←g.toMetricSpace_ball]
    exact Metric.isOpen_ball.measurableSet.preimage hf
  have hcover' : (univ:Set X) ⊆ ⋃ q∈(Finset.univ:Finset S), f ⁻¹' g.ball (f (center q)) r := by
    intro x _
    obtain ⟨q,hq,hx⟩ := mem_iUnion₂.mp (hcover (hinside x))
    exact mem_iUnion₂.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,hcenter ⟨q,hq⟩ x hx⟩
  have hs := Poincare.CurvatureIntegral.integral_le_card_mul_weighted_bound_of_finset_cover
    (μ := μ) (R := R) (K := K) (E := univ) (W := univ) MeasurableSet.univ
    (Finset.univ:Finset S)
    (fun q => f ⁻¹' g.ball (f (center q)) r)
    (fun q => f ⁻¹' g.ball (f (center q)) (2*r))
    (fun q _ => hmeas _ _) hRn hKn hRi.integrableOn
    (fun _ _ => hRi.integrableOn) hKi.integrableOn hcover'
    (fun _ _ => subset_univ _) hB (fun q _ => hbound (center q))
  simp only [Measure.restrict_univ,Finset.card_univ,Fintype.card_coe] at hs
  refine hs.trans ?_
  apply mul_le_mul_of_nonneg_right _ (add_nonneg zero_le_one (integral_nonneg hKn))
  apply mul_le_mul_of_nonneg_right _ hB
  have hcard' : S.card ≤ ⌈modelVolume n 1 6 / modelVolume n 1 (r/4)⌉₊ := by
    simpa only [show (3:ℝ)*2=6 by norm_num,show r/2/2=r/4 by ring] using hcard
  exact_mod_cast hcard'
