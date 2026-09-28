import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Estimates.Local

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_source_neck_quarter_derivative_bound
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {epsilon K : ℝ} (hepsilon : 0 < epsilon) (hK : 0 < K) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (F : RicciFlow 3 M (Icc (-(1 / 2 : ℝ)) 0))
        (N : EpsilonNeck (F.metric 0)),
        N.scale = 1 → N.epsilon = epsilon →
        (∀ t ∈ Icc (-(1 / 2 : ℝ)) 0, ∀ x : M,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ s ∈ Icc (-(1 / 4 : ℝ)) 0,
          ∀ q ∈ (F.metric 0).ball N.center (epsilon⁻¹ / 16),
            (F.connection s).curvatureDerivativeNorm m q ≤ B := by
  let L : ℝ := Real.exp (3 * K / 2)
  let r : ℝ := (epsilon⁻¹ / 32) / L
  have hL : 0 < L := Real.exp_pos _
  have heinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hr : 0 < r := div_pos (by positivity) hL
  obtain ⟨C, hC, hbound⟩ := hShi 3 m K K r hK hK hr
  refine ⟨C / (1 / 4 : ℝ) ^ ((m : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ F N hscale heps hRm s hs q hq
  have hnorm (x : M) (v : TangentSpace (𝓡 3) x) :
      (F.metric 0).tangentNorm x v ≤ L * (F.metric (-(1 / 2 : ℝ))).tangentNorm x v := by
    have h := (M04.tangentNorm_comparison_at_of_curvature_bound F
      (by norm_num : (-(1 / 2 : ℝ)) ∈ Icc (-(1 / 2 : ℝ)) 0)
      (by norm_num : (0 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) 0)
      (by norm_num) hK.le x (fun t ht => hRm t ht x) v).2
    convert h using 1
    congr 2
    norm_num [L]
    ring
  have hLr : L * r = epsilon⁻¹ / 32 := by
    dsimp only [r]
    field_simp
  have hsmall : (F.metric (-(1 / 2 : ℝ))).ball q r ⊆
      (F.metric 0).ball q (epsilon⁻¹ / 32) := by
    rw [← hLr]
    exact RiemannianMetric.ball_subset_ball_of_tangentNorm_le
      (F.metric (-(1 / 2 : ℝ))) (F.metric 0) q r L hL
        (fun x _ v => hnorm x v)
  have houter : (F.metric (-(1 / 2 : ℝ))).ball q r ⊆
      (F.metric 0).ball N.center (epsilon⁻¹ / 8) := by
    intro x hx
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    change (F.metric 0).edist N.center x < ENNReal.ofReal (epsilon⁻¹ / 8)
    calc
      (F.metric 0).edist N.center x ≤
          (F.metric 0).edist N.center q + (F.metric 0).edist q x :=
        Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal (epsilon⁻¹ / 16) + ENNReal.ofReal (epsilon⁻¹ / 32) :=
        ENNReal.add_lt_add hq (hsmall hx)
      _ = ENNReal.ofReal (epsilon⁻¹ / 16 + epsilon⁻¹ / 32) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (epsilon⁻¹ / 8) :=
        ENNReal.ofReal_le_ofReal (by linarith)
  have hcompact : IsCompact (closure ((F.metric (-(1 / 2 : ℝ))).ball q r)) := by
    have htop : IsCompact (closure ((F.metric 0).ball N.center (epsilon⁻¹ / 8))) := by
      simpa only [hscale, heps, one_mul] using
        (N.precompact_ball_of_central_sphere N.center_on_central_sphere).1
    exact htop.of_isClosed_subset isClosed_closure (closure_mono houter)
  have hshift : (fun s : ℝ => s + (-(1 / 2 : ℝ))) '' Icc 0 (1 / 2 : ℝ) ⊆
      Icc (-(1 / 2 : ℝ)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  let G := F.translate (-(1 / 2 : ℝ)) hshift ordConnected_Icc
    ⟨0, by norm_num, 1 / 2, by norm_num, by norm_num⟩
  have hmetric : G.metric 0 = F.metric (-(1 / 2 : ℝ)) := by
    change F.metric (0 + -(1 / 2 : ℝ)) = _
    rw [zero_add]
  have hcurv : ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∀ x ∈ (G.metric 0).ball q r,
      (G.connection t).curvatureTensorNorm x ≤ K := by
    intro t ht x _
    exact hRm (t + -(1 / 2 : ℝ)) (hshift ⟨t, ht, rfl⟩) x
  have hqsmall : q ∈ (G.metric 0).ball q (r / 2) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(G.metric 0).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) q q < ENNReal.ofReal (r / 2)
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (half_pos hr)
  have htime : s + 1 / 2 ∈ Ioc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [hs.1, hs.2]
  have hd := hbound M (1 / 2) (by norm_num)
    (by rw [div_self hK.ne']; norm_num) G q (hmetric.symm ▸ hcompact) hcurv
    (s + 1 / 2) htime q hqsmall
  change (F.connection (s + 1 / 2 + -(1 / 2 : ℝ))).curvatureDerivativeNorm m q ≤
    C / (s + 1 / 2) ^ ((m : ℝ) / 2) at hd
  rw [show s + 1 / 2 + -(1 / 2 : ℝ) = s by ring] at hd
  refine hd.trans (div_le_div_of_nonneg_left hC.le (by positivity) ?_)
  exact Real.rpow_le_rpow (by norm_num) (by linarith [hs.1]) (by positivity)

theorem exists_source_neck_terminal_derivative_bound
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {epsilon K : ℝ} (hepsilon : 0 < epsilon) (hK : 0 < K) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (F : RicciFlow 3 M (Icc (-(1 / 2 : ℝ)) 0))
        (N : EpsilonNeck (F.metric 0)),
        N.scale = 1 → N.epsilon = epsilon →
        (∀ t ∈ Icc (-(1 / 2 : ℝ)) 0, ∀ x : M,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ q ∈ (F.metric 0).ball N.center (epsilon⁻¹ / 16),
          (F.connection 0).curvatureDerivativeNorm m q ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_source_neck_quarter_derivative_bound hShi hepsilon hK m
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ _ F N hscale heps hRm q hq
  exact hbound M F N hscale heps hRm 0 (by norm_num) q hq

end PoincareConjecture.M28
