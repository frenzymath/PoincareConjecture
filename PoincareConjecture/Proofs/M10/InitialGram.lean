import PoincareConjecture.Proofs.M10.SquareComparison
import PoincareConjecture.Proofs.M10.MetricTrace
import PoincareConjecture.Proofs.M10.InitialJacobianCalculus
import PoincareConjecture.Proofs.M10.ExponentialTransport

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponential_scaled_gram_tendsto (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun s : ℝ ↦ (s⁻¹) ^ 2 • (fun i j : Fin n ↦
      pullbackMetricForm (F.metric (T - s ^ 2)) (exponentialSliceChart G (s ^ 2)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := metricCoordinates (F.metric T) p
  let Z := β x
  let W := fun i : Fin n ↦ β (EuclideanSpace.basisFun (Fin n) ℝ i)
  let L := (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ p
  let B := fun s : ℝ ↦ backwardMetricCoordinates F T p (G.squareFamily Z s, s ^ 2)
  let B₀ := backwardMetricCoordinates F T p (p, 0)
  let V := fun (i : Fin n) (s : ℝ) ↦
    s⁻¹ • fderiv ℝ (squareCoordinates G) (Z, s) (W i, 0)
  have hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 B₀) :=
    squareMetric_tendsto_zero G hmax hT hwindow Z
  have hV (i : Fin n) : Tendsto (V i) (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ) • L (W i))) :=
    squareCoordinates_scaled_differential_tendsto G hmax Z (W i)
  have hchart : ∀ᶠ s in 𝓝[>] (0 : ℝ), G.squareFamily Z s ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
    ((squareFamily_tendsto_zero G hmax Z).mono_left nhdsWithin_le_nhds)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds (mem_chart_source _ _))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have heval₁ : Continuous (fun z :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ×
        EuclideanSpace ℝ (Fin n) ↦ z.1 z.2) := continuous_fst.clm_apply continuous_snd
  have heval₂ : Continuous (fun z :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × EuclideanSpace ℝ (Fin n) ↦ z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hpair := heval₂.continuousAt.tendsto.comp
    ((heval₁.continuousAt.tendsto.comp (hB.prodMk_nhds (hV i))).prodMk_nhds (hV j))
  have hvalue : B₀ ((2 : ℝ) • L (W i)) ((2 : ℝ) • L (W j)) =
      (4 : ℝ) * (if i = j then 1 else 0) := by
    have heq := backwardMetricCoordinates_apply (F := F) (T := T) p (p, 0)
      (mem_chart_source _ _) ((2 : ℝ) • W i) ((2 : ℝ) • W j)
    simp only [map_smul, smul_apply, smul_eq_mul, sub_zero] at heq
    have hinner := metricCoordinates_basis_inner (F.metric T) p i j
    change (F.metric T).inner p (W i) (W j) = _ at hinner
    change B₀ (2 • L (W i)) (2 • L (W j)) = _
    simp only [map_smul, smul_apply, smul_eq_mul]
    change 2 * (2 * B₀ (L (W i)) (L (W j))) =
      2 * (2 * (F.metric T).inner p (W i) (W j)) at heq
    rw [heq, hinner]
    ring
  simp only [Function.comp_def, hvalue] at hpair
  apply hpair.congr'
  filter_upwards [Ioo_mem_nhdsGT (Real.sqrt_pos.2 hmax), hchart] with s hs hqs
  have hq : G.gamma Z (s ^ 2) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
    rwa [G.square_agrees Z s ⟨hs.1.le, hs.2⟩] at hqs
  change B s (s⁻¹ • _) (s⁻¹ • _) = _
  simp only [map_smul, smul_apply, smul_eq_mul]
  change s⁻¹ * (s⁻¹ * _) = s⁻¹ ^ 2 *
    pullbackMetricForm (F.metric (T - s ^ 2)) (exponentialSliceChart G (s ^ 2)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  rw [squareCoordinates_pullbackMetric_eq G hmax x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) hs hq]
  ring

theorem exponential_scaled_jacobian_tendsto (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun s : ℝ ↦ (s ^ n)⁻¹ * exponentialSliceJacobian G (s ^ 2) x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ) ^ n)) :=
  tendsto_scaled_sqrt_det (exponential_scaled_gram_tendsto G hmax hT hwindow x)

end PoincareConjecture.M10
