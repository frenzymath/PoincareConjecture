import PoincareConjecture.Proofs.M15.Prop8_2_CylinderDistance
import PoincareConjecture.Proofs.M15.Mathlib.CompactBuffer











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]



theorem actualBallCylinder_normalized_domain
    (B : M15ActualBallCylinder G T x r K C) (hQ : 0 < r⁻¹ ^ 2) :
    (parabolicInterval (r⁻¹ ^ 2) hQ (T - r ^ 2) K).domain = Set.Icc 0 1 := by
  rw [parabolicInterval_domain, B.interval_domain]
  change (parabolicTimeOrderIso (r⁻¹ ^ 2) hQ (T - r ^ 2)) ''
    Set.Icc (T - r ^ 2) T = _
  rw [OrderIso.image_Icc]
  simp only [parabolicTimeOrderIso_apply, parabolicTime, sub_self, mul_zero]
  congr 1
  field_simp [B.radius_pos.ne']
  ring



theorem actualBallCylinder_normalized_curvature_le_one
    (B : M15ActualBallCylinder G T x r K C)
    (F : RicciFlow n C K.domain)
    (hRm : ∀ (t : (G.timeIntervals.interval K).Point) (c : C),
      (F.connection t.val).curvatureTensorNorm c =
        horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (t, c)))
    (hQ : 0 < r⁻¹ ^ 2)
    (R : OrdinaryParabolicRescaling F (r⁻¹ ^ 2) hQ (T - r ^ 2))
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) (c : C) :
    (R.flow.connection s).curvatureTensorNorm c ≤ 1 := by
  let : LocallyCompactSpace C :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) C
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  have hsR : s ∈ (parabolicInterval (r⁻¹ ^ 2) hQ (T - r ^ 2) K).domain := by
    rwa [actualBallCylinder_normalized_domain B hQ]
  have ht := (mem_parabolicInterval_iff (r⁻¹ ^ 2) hQ (T - r ^ 2) K s).mp hsR
  have hbound : (F.connection (parabolicTimeInv (r⁻¹ ^ 2) (T - r ^ 2) s)).curvatureTensorNorm c
      ≤ r⁻¹ ^ 2 := by
    rw [hRm ⟨_, ht⟩ c]
    exact B.curvature_bound ⟨_, ht⟩ c
  have hscale := (R.metric_calculus s).curvature_norm_eq
    (F.connection (parabolicTimeInv (r⁻¹ ^ 2) (T - r ^ 2) s))
    (R.flow.connection s) c
  change (R.flow.connection s).curvatureTensorNorm c = _ at hscale
  rw [hscale, div_le_iff₀ hQ, one_mul]
  exact hbound




theorem actualBallCylinder_normalized_terminal_edist_le
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (F : RicciFlow n C K.domain) (hmetric : F.metric = B.metric.metric)
    (hRm : ∀ (t : (G.timeIntervals.interval K).Point) (c : C),
      (F.connection t.val).curvatureTensorNorm c =
        horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (t, c)))
    (hQ : 0 < r⁻¹ ^ 2)
    (R : OrdinaryParabolicRescaling F (r⁻¹ ^ 2) hQ (T - r ^ 2)) (c d : C) :
    (G.slices T).metricOnPoints.edist (B.source_map c) (B.source_map d) ≤
      ENNReal.ofReal (r * Real.exp (n : ℝ)) * (R.flow.metric 0).edist c d := by
  let : LocallyCompactSpace C :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) C
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  have ha : T - r ^ 2 ∈ K.domain := by
    rw [B.interval_domain]
    exact ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩
  have hdist := actualBallCylinder_terminal_edist_le hM12 B F hmetric hRm ha c d
  have hexp : (n : ℝ) * (r⁻¹) ^ 2 * (T - (T - r ^ 2)) = n := by
    field_simp [B.radius_pos.ne']
    ring
  rw [hexp] at hdist
  have hscale := (R.metric_calculus 0).edist_eq c d
  change (R.flow.metric 0).edist c d =
    ENNReal.ofReal (Real.sqrt (r⁻¹ ^ 2)) *
      (F.metric (parabolicTimeInv (r⁻¹ ^ 2) (T - r ^ 2) 0)).edist c d at hscale
  simp only [Real.sqrt_sq (inv_nonneg.mpr B.radius_pos.le),
    parabolicTimeInv, zero_div, add_zero] at hscale
  have horig : (F.metric (T - r ^ 2)).edist c d =
      ENNReal.ofReal r * (R.flow.metric 0).edist c d := by
    rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul B.radius_pos.le,
      mul_inv_cancel₀ B.radius_pos.ne', ENNReal.ofReal_one, one_mul]
  rw [horig] at hdist
  simpa only [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    mul_comm (Real.exp (n : ℝ)) r] using hdist




theorem actualBallCylinder_normalized_initial_precompact
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (F : RicciFlow n C K.domain) (hmetric : F.metric = B.metric.metric)
    (hRm : ∀ (t : (G.timeIntervals.interval K).Point) (c : C),
      (F.connection t.val).curvatureTensorNorm c =
        horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (t, c)))
    (hQ : 0 < r⁻¹ ^ 2)
    (R : OrdinaryParabolicRescaling F (r⁻¹ ^ 2) hQ (T - r ^ 2))
    (hcompact : IsCompact (closure ((G.slices T).metricOnPoints.ball x r)))
    {c : C} (hc : B.source_map c ∈ (G.slices T).metricOnPoints.ball x (r / 2)) :
    IsCompact (closure ((R.flow.metric 0).ball c (Real.exp (-(n : ℝ)) / 8))) := by
  have hr : 0 < r := B.radius_pos
  let : LocallyCompactSpace C :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) C
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C → Type _) :=
    ⟨(R.flow.metric 0).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : C → Type _) :=
    ⟨⟨(R.flow.metric 0).inner, (R.flow.metric 0).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace C := .ofRiemannianMetric (𝓡 n) C
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
    ⟨(G.slices T).metricOnPoints.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
    ⟨⟨(G.slices T).metricOnPoints.inner,
      (G.slices T).metricOnPoints.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace (G.slices T).Point :=
    .ofRiemannianMetric (𝓡 n) (G.slices T).Point
  have hsourceball : (R.flow.metric 0).ball c (Real.exp (-(n : ℝ)) / 8) =
      Metric.eball c (ENNReal.ofReal (Real.exp (-(n : ℝ)) / 8)) := by
    ext z
    change edist c z < _ ↔ edist z c < _
    rw [edist_comm c z]
  have htargetball (q : ℝ) : (G.slices T).metricOnPoints.ball x q =
      Metric.eball x (ENNReal.ofReal q) := by
    ext z
    change edist x z < _ ↔ edist z x < _
    rw [edist_comm x z]
  rw [hsourceball]
  let L : ℝ≥0 := ⟨r * Real.exp (n : ℝ), mul_nonneg B.radius_pos.le (Real.exp_pos _).le⟩
  have hL : (L : ℝ≥0∞) = ENNReal.ofReal (r * Real.exp (n : ℝ)) :=
    ENNReal.ofReal_coe_nnreal.symm
  apply Metric.isCompact_closure_eball_of_isEmbedding B.source_map_embedding
    (x := x) (R := ENNReal.ofReal r)
    (r₀ := ENNReal.ofReal (r / 2)) (r₁ := ENNReal.ofReal (3 * r / 4))
    (L := L)
  · simpa only [htargetball] using B.source_map_range
  · simpa only [htargetball] using hcompact
  · exact (show edist x (B.source_map c) < ENNReal.ofReal (r / 2) from hc).le
  · intro z
    rw [hL]
    exact actualBallCylinder_normalized_terminal_edist_le hM12 B F hmetric hRm hQ R c z
  · rw [hL, ← ENNReal.ofReal_mul (mul_nonneg B.radius_pos.le (Real.exp_pos _).le),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      _ = r / 2 + r * (Real.exp (n : ℝ) * Real.exp (-(n : ℝ))) / 8 := by ring
      _ = 5 * r / 8 := by rw [he]; ring
      _ ≤ 3 * r / 4 := by linarith [B.radius_pos]
  · exact ENNReal.ofReal_lt_ofReal_iff B.radius_pos |>.mpr (by linarith [B.radius_pos])

end PoincareConjecture.Proofs.M15
