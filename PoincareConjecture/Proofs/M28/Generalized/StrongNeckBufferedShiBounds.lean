import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSlabRegularity
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Estimates.Local












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28






theorem exists_source_neck_buffered_core_derivative_bound
    (hShi : LocalCurvatureDerivativeEstimates.{u})
    {epsilon K : ℝ} (hepsilon : 0 < epsilon) (hK : 0 < K) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (F : RicciFlow 3 M (Icc (-(3 / 4 : ℝ)) 0))
        (N : EpsilonNeck (F.metric 0)),
        N.scale = 1 → N.epsilon = epsilon →
        (∀ t ∈ Icc (-(3 / 4 : ℝ)) 0, ∀ x : M,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ s ∈ Icc (-(5 / 8 : ℝ)) 0, ∀ q ∈ N.carrier,
          |(N.coordinate_inverse q).2| ≤ 3 * epsilon⁻¹ / 4 →
            (F.connection s).curvatureDerivativeNorm m q ≤ B := by
  let L : ℝ := Real.exp (9 * K / 4)
  let r : ℝ := (epsilon⁻¹ / 16) / L
  have hL : 0 < L := Real.exp_pos _
  have heinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hr : 0 < r := div_pos (by positivity) hL
  obtain ⟨C, hC, hbound⟩ := hShi 3 m K K r hK hK hr
  refine ⟨C / (1 / 8 : ℝ) ^ ((m : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ F N hscale heps hRm s hs q hq hheight
  have hepshalf : epsilon < 1 / 2 := heps ▸ N.epsilon_lt_half
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - epsilon) := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1 - epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - epsilon)]
  have hterminal : IsCompact (closure ((F.metric 0).ball q (epsilon⁻¹ / 16))) := by
    apply (N.precompact_ball_of_axial_margin hq ?_).1
    rw [hscale, heps, one_mul]
    have hmargin : epsilon⁻¹ / 4 ≤ epsilon⁻¹ - |(N.coordinate_inverse q).2| := by
      linarith only [hheight]
    have hlower := mul_le_mul hroot hmargin
      (by positivity : 0 ≤ epsilon⁻¹ / 4) (Real.sqrt_nonneg (1 - epsilon))
    nlinarith only [hlower, heinv]
  have hnorm (x : M) (v : TangentSpace (𝓡 3) x) :
      (F.metric 0).tangentNorm x v ≤ L * (F.metric (-(3 / 4 : ℝ))).tangentNorm x v := by
    have h := (M04.tangentNorm_comparison_at_of_curvature_bound F
      (by norm_num : (-(3 / 4 : ℝ)) ∈ Icc (-(3 / 4 : ℝ)) 0)
      (by norm_num : (0 : ℝ) ∈ Icc (-(3 / 4 : ℝ)) 0)
      (by norm_num) hK.le x (fun t ht => hRm t ht x) v).2
    convert h using 1
    congr 2
    norm_num [L]
    ring
  have hLr : L * r = epsilon⁻¹ / 16 := by
    dsimp only [r]
    field_simp
  have hsmall : (F.metric (-(3 / 4 : ℝ))).ball q r ⊆
      (F.metric 0).ball q (epsilon⁻¹ / 16) := by
    rw [← hLr]
    exact RiemannianMetric.ball_subset_ball_of_tangentNorm_le
      (F.metric (-(3 / 4 : ℝ))) (F.metric 0) q r L hL
        (fun x _ v => hnorm x v)
  have hcompact : IsCompact (closure ((F.metric (-(3 / 4 : ℝ))).ball q r)) :=
    hterminal.of_isClosed_subset isClosed_closure (closure_mono hsmall)
  have hshift : (fun s : ℝ => s + (-(3 / 4 : ℝ))) '' Icc 0 (3 / 4 : ℝ) ⊆
      Icc (-(3 / 4 : ℝ)) 0 := by
    rintro _ ⟨t, ht, rfl⟩
    constructor <;> linarith [ht.1, ht.2]
  let G := F.translate (-(3 / 4 : ℝ)) hshift ordConnected_Icc
    ⟨0, by norm_num, 3 / 4, by norm_num, by norm_num⟩
  have hmetric : G.metric 0 = F.metric (-(3 / 4 : ℝ)) := by
    change F.metric (0 + -(3 / 4 : ℝ)) = _
    rw [zero_add]
  have hcurv : ∀ t ∈ Icc (0 : ℝ) (3 / 4), ∀ x ∈ (G.metric 0).ball q r,
      (G.connection t).curvatureTensorNorm x ≤ K := by
    intro t ht x _
    exact hRm (t + -(3 / 4 : ℝ)) (hshift ⟨t, ht, rfl⟩) x
  have hqsmall : q ∈ (G.metric 0).ball q (r / 2) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(G.metric 0).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) q q < ENNReal.ofReal (r / 2)
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (half_pos hr)
  have htime : s + 3 / 4 ∈ Ioc (0 : ℝ) (3 / 4) := by
    constructor <;> linarith [hs.1, hs.2]
  have hd := hbound M (3 / 4) (by norm_num)
    (by rw [div_self hK.ne']; norm_num) G q (hmetric.symm ▸ hcompact) hcurv
    (s + 3 / 4) htime q hqsmall
  change (F.connection (s + 3 / 4 + -(3 / 4 : ℝ))).curvatureDerivativeNorm m q ≤
    C / (s + 3 / 4) ^ ((m : ℝ) / 2) at hd
  rw [show s + 3 / 4 + -(3 / 4 : ℝ) = s by ring] at hd
  refine hd.trans (div_le_div_of_nonneg_left hC.le (by positivity) ?_)
  exact Real.rpow_le_rpow (by norm_num) (by linarith [hs.1]) (by positivity)

end PoincareConjecture.M28
