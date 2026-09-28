import PoincareConjecture.Proofs.M15.Prop8_2_CurvatureContractions
import PoincareConjecture.Proofs.M15.Prop8_2_NormalizedCylinder
import PoincareConjecture.Proofs.M15.Prop8_2_ScalarTransport
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_unit_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [SecondCountableTopology M]
        (F : RicciFlow n M (Set.Icc 0 1)) (c : M),
        IsCompact (closure ((F.metric 0).ball c (Real.exp (-(n : ℝ)) / 8))) →
        (∀ s ∈ Set.Icc 0 1, ∀ z : M, (F.connection s).curvatureTensorNorm z ≤ 1) →
        ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) c,
          |mvfderiv (𝓡 n) (F.connection s).scalarCurvature c v| ≤
            A * (F.metric s).tangentNorm c v := by
  have hρ : 0 < Real.exp (-(n : ℝ)) / 8 := by positivity
  obtain ⟨A, hA, hShi⟩ := hM04.local_derivative_estimates n 1 1 1
    (Real.exp (-(n : ℝ)) / 8) zero_lt_one zero_lt_one hρ
  refine ⟨1 + 2 * (n : ℝ) ^ 2 * A, by positivity, ?_⟩
  intro M _ _ _ _ _ F c hcompact hRm s hs v
  have hc : c ∈ (F.metric 0).ball c ((Real.exp (-(n : ℝ)) / 8) / 2) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 n) c c < _
    rw [Manifold.riemannianEDist_self, ENNReal.ofReal_pos]
    positivity
  have hs0 : 0 < s := by linarith [hs.1]
  have hder := hShi M 1 zero_lt_one (by norm_num) F c hcompact
    (fun t ht z _ => hRm t ht z) s ⟨hs0, hs.2⟩ c hc
  simp only [Nat.cast_one, ← Real.sqrt_eq_rpow] at hder
  have hsqrt : 1 / 2 ≤ Real.sqrt s := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s, hs.1]
  have hder' : (F.connection s).curvatureDerivativeNorm 1 c ≤ 2 * A := by
    apply hder.trans
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hs0)).mpr
    nlinarith
  have hN : 0 ≤ (F.metric s).tangentNorm c v := Real.sqrt_nonneg _
  calc
    _ ≤ (n : ℝ) ^ 2 * (F.connection s).curvatureDerivativeNorm 1 c *
        (F.metric s).tangentNorm c v :=
      abs_scalarCurvature_derivative_le_curvatureDerivativeNorm (F.connection s) c v
    _ ≤ (n : ℝ) ^ 2 * (2 * A) * (F.metric s).tangentNorm c v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hder' (sq_nonneg _)) hN
    _ ≤ (1 + 2 * (n : ℝ) ^ 2 * A) * (F.metric s).tangentNorm c v := by
      nlinarith

theorem exists_actualBallCylinder_horizontal_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) (n : ℕ)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
        (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport n X time I)
        (T : ℝ) (x : (G.slices T).Point) (r : ℝ) (K : SpacetimeInterval)
        (C : Type u) [TopologicalSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
        [T2Space C] [SecondCountableTopology C]
        (B : M15ActualBallCylinder G T x r K C),
        IsCompact (closure ((G.slices T).metricOnPoints.ball x r)) →
        ∀ t : (G.timeIntervals.interval K).Point, T - r ^ 2 / 2 ≤ t.val →
        ∀ c : C, B.source_map c ∈ (G.slices T).metricOnPoints.ball x (r / 2) →
        ∀ w : G.Horizontal (B.embedding.toSpacetime (t, c)),
          |M14HorizontalScalarDifferential G (B.embedding.toSpacetime (t, c)) w.val| ≤
            (A / r ^ 3) * Real.sqrt
              (G.spacetime.horizontalMetric.inner (B.embedding.toSpacetime (t, c)) w w) := by
  obtain ⟨A, hA, hunit⟩ := exists_unit_scalar_gradient_bound hM04 n
  refine ⟨A, hA, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact t ht c hc w
  have hr : 0 < r := B.radius_pos
  let : LocallyCompactSpace C :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) C
  let : RegularSpace C :=
    .of_hasBasis compact_basis_nhds fun _ _ h => h.2.isClosed
  let : T3Space C := ⟨⟩
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  obtain ⟨F, hmetric, hRm, hscalar⟩ := actualBallCylinder_exists_flow hM12 B
  let Q : ℝ := r⁻¹ ^ 2
  have hQ : 0 < Q := pow_pos (inv_pos.mpr hr) 2
  let a : ℝ := T - r ^ 2
  obtain ⟨R⟩ := hM13.ordinary_flow C K F Q hQ a
  have hdom : (parabolicInterval Q hQ a K).domain = Set.Icc 0 1 :=
    actualBallCylinder_normalized_domain B hQ
  let F₁ : RicciFlow n C (Set.Icc 0 1) :=
    { metric := R.flow.metric
      connection := R.flow.connection
      interval := by rw [← hdom]; exact R.flow.interval
      nontrivial := by rw [← hdom]; exact R.flow.nontrivial
      smooth := by rw [← hdom]; exact R.flow.smooth
      equation := by
        intro s hs z u v
        have hsR : s ∈ (parabolicInterval Q hQ a K).domain := by rwa [hdom]
        simpa only [hdom] using R.flow.equation s hsR z u v }
  have hK : IsCompact (closure ((F₁.metric 0).ball c (Real.exp (-(n : ℝ)) / 8))) :=
    actualBallCylinder_normalized_initial_precompact hM12 B F hmetric hRm hQ R hcompact hc
  have hRm₁ : ∀ s ∈ Set.Icc 0 1, ∀ z : C, (F₁.connection s).curvatureTensorNorm z ≤ 1 :=
    fun _ hs z => actualBallCylinder_normalized_curvature_le_one B F hRm hQ R hs z
  let s : ℝ := parabolicTime Q a t.val
  have htK : t.val ∈ Set.Icc (T - r ^ 2) T := by
    rw [← B.interval_domain]
    exact t.property
  have hQtime : Q * r ^ 2 = 1 := by
    dsimp only [Q]
    field_simp [hr.ne']
  have hlow : r ^ 2 / 2 ≤ t.val - a := by dsimp only [a]; linarith
  have hupp : t.val - a ≤ r ^ 2 := by dsimp only [a]; linarith [htK.2]
  have hs : s ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    dsimp only [s, parabolicTime, Set.mem_Icc]
    constructor <;> nlinarith only [hQtime,
      mul_le_mul_of_nonneg_left hlow hQ.le, mul_le_mul_of_nonneg_left hupp hQ.le]
  have hsR : s ∈ (parabolicInterval Q hQ a K).domain := by
    rw [hdom]
    exact ⟨by linarith [hs.1], hs.2⟩
  have htime : parabolicTimeInv Q a s = t.val :=
    parabolicTimeInv_parabolicTime Q hQ a t.val
  obtain ⟨v, rfl⟩ := (B.metric.spatialTangentEquiv t c).surjective w
  have hgrad := hunit C F₁ c hK hRm₁ s hs v
  change |mvfderiv (𝓡 n) (R.flow.connection s).scalarCurvature c v| ≤
    A * (R.flow.metric s).tangentNorm c v at hgrad
  have hD := rescaling_scalarDifferential_eq hM04 F Q hQ a R s hsR c v
  rw [htime] at hD
  have hNscale : (R.flow.metric s).tangentNorm c v =
      r⁻¹ * (F.metric t.val).tangentNorm c v := by
    have h := (R.metric_calculus s).tangent_norm c v
    simp only [Diffeomorph.coe_refl, id_eq, mfderiv_id] at h
    change (R.flow.metric s).tangentNorm c v =
      Real.sqrt Q * (F.metric (parabolicTimeInv Q a s)).tangentNorm c v at h
    simpa only [Q, Real.sqrt_sq (inv_nonneg.mpr hr.le), htime] using h
  have hN : (F.metric t.val).tangentNorm c v =
      Real.sqrt (G.spacetime.horizontalMetric.inner (B.embedding.toSpacetime (t, c))
        (B.metric.spatialTangentEquiv t c v) (B.metric.spatialTangentEquiv t c v)) := by
    rw [hmetric]
    exact congrArg Real.sqrt (B.metric.metric_eq t c v v)
  rw [← actualBallCylinder_scalarDifferential_pullback hM12 B F hscalar t c v,
    hD, abs_mul, abs_of_pos hQ]
  apply (mul_le_mul_of_nonneg_left hgrad hQ.le).trans_eq
  rw [hNscale, ← mul_assoc, ← mul_assoc]
  have hcoeff : Q * A * r⁻¹ = A / r ^ 3 := by
    dsimp only [Q]
    field_simp [hr.ne']
  rw [hcoeff, hN]

end PoincareConjecture.Proofs.M15
