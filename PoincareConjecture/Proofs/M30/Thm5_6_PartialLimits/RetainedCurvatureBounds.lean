import PoincareConjecture.Proofs.M30.Thm3_28.FiniteCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.CompactBallTransfer
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.secondCountable

set_option maxHeartbeats 600000 in




theorem exists_eventually_retained_curvature_derivative_bound
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {n : ℕ} {T Tbig B : ℝ} (hT : 0 < T) (hTT : T < Tbig)
    {S : PointedFlowSequence n (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (Fbig : ∀ k, RicciFlow n (S.carrier k).carrier (Icc (-Tbig) 0))
    (hmetric : ∀ k, (Fbig k).metric (-T / 2) = (S.flow k).metricAt 0)
    (hcurv : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-Tbig) 0,
      ∀ x : (S.carrier k).carrier,
        ((Fbig k).connection t).curvatureTensorNorm x ≤ B)
    (hcompact : ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (((Fbig k).metric 0).ball (S.flow k).base R)))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
        ((Fbig (G.subsequence k)).connection t).curvatureDerivativeNorm m
          (((G.embedding k).toFun (0, x)).2) ≤ D := by
  have hTbig : 0 < Tbig := hT.trans hTT
  have hzero : -T / 2 < 0 ∧ 0 < T / 2 := ⟨by linarith, by linarith⟩
  obtain ⟨R, hR, hcapture⟩ :=
    G.exists_pos_eventually_image_subset_ballAt hzero hzero hcomplete hK
  let L : ℝ := (n : ℝ) ^ 3 * max B 1
  let E : ℝ := Real.exp (L * Tbig)
  let rho : ℝ := E * (R + 1)
  have hL : 0 ≤ L := mul_nonneg (by positivity)
    (zero_le_one.trans (le_max_right B 1))
  have hE : 0 < E := Real.exp_pos _
  have hrho : 0 < rho := mul_pos hE (by linarith)
  have href : -T / 2 ∈ Icc (-Tbig) (0 : ℝ) := ⟨by linarith, by linarith⟩
  have hterminal : (0 : ℝ) ∈ Icc (-Tbig) 0 := ⟨by linarith, le_rfl⟩
  have hinitial : -Tbig ∈ Icc (-Tbig) (0 : ℝ) := ⟨le_rfl, by linarith⟩
  obtain ⟨D, hD, hShiBound⟩ :=
    exists_uniform_curvatureDerivativeNorm_bound_on_buffered_cylinders
      hShi n m B Tbig 1 (Tbig - T) hTbig zero_lt_one (sub_pos.mpr hTT)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hcapture,
    G.subsequence_strictMono.tendsto_atTop.eventually hcurv,
    G.subsequence_strictMono.tendsto_atTop.eventually (hcompact rho hrho)]
    with k hk hck hcompactk
  let F := Fbig (G.subsequence k)
  let p := (S.flow (G.subsequence k)).base
  let ψ : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun x => ((G.embedding k).toFun (0, x)).2
  have hRic (s : ℝ) (hs : s ∈ Icc (-Tbig) 0)
      (y : (S.carrier (G.subsequence k)).carrier) (v : TangentSpace (𝓡 n) y) :
      |(F.connection s).ricci y v v| ≤ L * (F.metric s).inner y v v := by
    have hQ : 0 ≤ (F.metric s).inner y v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact ((F.metric s).pos y v hv).le
    have hnorm := (F.connection s).abs_ricci_quadratic_le_curvatureTensorNorm y v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) y) = n :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((hck s hs y).trans (le_max_left B 1))
        (by positivity)) hQ)
  have hcaptured (x : G.limitCarrier.carrier) (hx : x ∈ K) :
      ψ x ∈ (F.metric 0).ball p (E * R) := by
    have hsource := hk (mem_image_of_mem ψ hx)
    change ψ x ∈ ((S.flow (G.subsequence k)).metricAt 0).ball p R at hsource
    rw [← hmetric] at hsource
    have hball := F.ball_subset_ball_of_ricci_bound (convex_Icc (-Tbig) 0)
      (Subset.refl _) p R L href hterminal (fun s hs y _ v => hRic s hs y v)
    have hdisplacement : |(0 : ℝ) - (-T / 2)| ≤ Tbig := by
      rw [zero_sub, abs_neg, abs_of_neg (by linarith : -T / 2 < 0)]
      linarith
    have hexp : Real.exp (L * |(0 : ℝ) - (-T / 2)|) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdisplacement hL)
    exact (hball hsource).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hexp hR.le))
  have hcompactInitial (y : (S.carrier (G.subsequence k)).carrier)
      (hy : y ∈ ψ '' K) : IsCompact (closure ((F.metric (-Tbig)).ball y 1)) := by
    obtain ⟨x, hx, rfl⟩ := hy
    apply hcompactk.of_isClosed_subset isClosed_closure
    apply closure_mono
    have hball : (F.metric (-Tbig)).ball (ψ x) 1 ⊆ (F.metric 0).ball (ψ x) E := by
      have h := F.ball_subset_ball_of_ricci_bound (convex_Icc (-Tbig) 0)
        (Subset.refl _) (ψ x) 1 L hinitial hterminal
        (fun s hs y _ v => hRic s hs y v)
      simpa only [zero_sub, neg_neg, abs_of_nonneg hTbig.le, mul_one] using h
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : (S.carrier (G.subsequence k)).carrier → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    intro z hz
    change (F.metric 0).edist p z < ENNReal.ofReal rho
    calc
      (F.metric 0).edist p z ≤
          (F.metric 0).edist p (ψ x) + (F.metric 0).edist (ψ x) z :=
        Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal (E * R) + ENNReal.ofReal E :=
        ENNReal.add_lt_add (hcaptured x hx) (hball hz)
      _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (mul_pos hE hR).le hE.le]
        congr 1
        dsimp only [rho]
        ring
  intro t ht x hx
  exact hShiBound (S.carrier (G.subsequence k)).carrier F (ψ '' K)
    hcompactInitial hck t ⟨by linarith [ht.1], ht.2⟩ (ψ x) (mem_image_of_mem ψ hx)

end PoincareConjecture.M30
