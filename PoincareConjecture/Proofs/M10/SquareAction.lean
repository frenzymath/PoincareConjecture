import PoincareConjecture.Proofs.M10.SquareComparison









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


noncomputable def squareKineticEnergy (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (s : ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let V := fderiv ℝ (squareCoordinates G) (Z, s) (0, 1)
  backwardMetricCoordinates F T p (G.squareFamily Z s, s ^ 2) V V

set_option backward.isDefEq.respectTransparency false in

theorem squareCoordinates_time_eq_endpoint
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (Z : TangentSpace (𝓡 n) p) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τmax))
    (hq : G.gamma Z (s ^ 2) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (squareCoordinates G) (Z, s) (0, 1) =
      (2 * s) • fderiv ℝ (endpointCoordinates G p) (Z, s ^ 2) (0, 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  have hqs : G.squareFamily Z s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
    rwa [G.square_agrees Z s ⟨hs.1.le, hs.2⟩]
  have hP := squareCoordinates_contDiffAt G (Z, s)
    (G.square_contains ⟨mem_univ _, hs.1.le, hs.2⟩) hqs
  have hE := endpointCoordinates_contDiffAt G p (Z, s ^ 2)
    ⟨mem_univ _, sq_pos_of_pos hs.1, hsmax⟩ hq
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hd := (hasDerivAt_time_slice (hE.differentiableAt (by simp))).scomp
    (h := fun r : ℝ ↦ r ^ 2) s hsq
  have heq : (fun r : ℝ ↦ squareCoordinates G (Z, r)) =ᶠ[𝓝 s]
      (fun r : ℝ ↦ endpointCoordinates G p (Z, r ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact congrArg (extChartAt (𝓡 n) p) (G.square_agrees Z r ⟨hr.1.le, hr.2⟩)
  exact (hasDerivAt_time_slice (hP.differentiableAt (by simp))).unique
    (hd.congr_of_eventuallyEq heq)

set_option backward.isDefEq.respectTransparency false in

theorem squareKineticEnergy_eq_speed
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (Z : TangentSpace (𝓡 n) p) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τmax))
    (hq : G.gamma Z (s ^ 2) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    squareKineticEnergy G Z s = (2 * s) ^ 2 *
      (F.metric (T - s ^ 2)).inner (G.gamma Z (s ^ 2))
        (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  unfold squareKineticEnergy
  rw [squareCoordinates_time_eq_endpoint G hmax Z hs hq,
    endpointCoordinates_time G p (Z, s ^ 2) ⟨mem_univ _, sq_pos_of_pos hs.1, hsmax⟩ hq,
    G.square_agrees Z s ⟨hs.1.le, hs.2⟩]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [backwardMetricCoordinates_apply p (G.gamma Z (s ^ 2), s ^ 2) hq]
  ring


theorem squareAction_hasDerivAt
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (Z : TangentSpace (𝓡 n) p) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τmax))
    (hq : G.gamma Z (s ^ 2) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun r : ℝ ↦ G.toLExponentialFamily.action Z (r ^ 2))
      (2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (G.gamma Z (s ^ 2)) +
        squareKineticEnergy G Z s / 2) s := by
  have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  apply ((G.action_time_derivative Z (s ^ 2) (sq_pos_of_pos hs.1) hsmax).comp
    (h := fun r : ℝ ↦ r ^ 2) s hsq).congr_deriv
  rw [squareKineticEnergy_eq_speed G hmax Z hs hq]
  simp only [backwardLIntegrand, Real.sqrt_sq hs.1.le]
  ring

set_option backward.isDefEq.respectTransparency false in

theorem squareKineticEnergy_tendsto_zero
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J) (Z : TangentSpace (𝓡 n) p) :
    Tendsto (squareKineticEnergy G Z) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * (F.metric T).inner p Z Z)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let V := fun s : ℝ ↦ fderiv ℝ (squareCoordinates G) (Z, s) (0, 1)
  let L := (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ p
  have hP := squareCoordinates_contDiffAt G (Z, 0) (squareDomain_at_zero G hmax Z)
    (by simpa only [G.square_at_zero] using mem_chart_source (EuclideanSpace ℝ (Fin n)) p)
  have hP2 : ContDiffAt ℝ 2 (squareCoordinates G) (Z, 0) := hP.of_le (by decide)
  have hV : ContinuousAt V 0 :=
    (((hP2.fderiv_right (m := 1) (by norm_num)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).clm_apply continuousAt_const)
  have hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ) • L Z)) := by
    have hv0 : V 0 = (2 : ℝ) • L Z := squareCoordinates_time_at_zero G hmax Z
    simpa only [hv0] using hV.tendsto.mono_left nhdsWithin_le_nhds
  have hB := squareMetric_tendsto_zero G hmax hT hwindow Z
  have heval : Continuous (fun z :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ×
        EuclideanSpace ℝ (Fin n) ↦ z.1 z.2 z.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hlim := heval.continuousAt.tendsto.comp (hB.prodMk_nhds hVlim)
  have hvalue : backwardMetricCoordinates F T p (p, 0) ((2 : ℝ) • L Z)
      ((2 : ℝ) • L Z) = 4 * (F.metric T).inner p Z Z := by
    have heq := backwardMetricCoordinates_apply (F := F) (T := T) p (p, 0)
      (mem_chart_source _ _) Z Z
    simp only [sub_zero] at heq
    simp only [map_smul, smul_apply, smul_eq_mul]
    change 2 * (2 * backwardMetricCoordinates F T p (p, 0) (L Z) (L Z)) = _
    rw [heq]
    ring
  change Tendsto (fun s : ℝ ↦
    backwardMetricCoordinates F T p (G.squareFamily Z s, s ^ 2) (V s) (V s))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 * (F.metric T).inner p Z Z))
  simpa only [Function.comp_def, hvalue] using hlim

end PoincareConjecture.M10
