import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurvePasting
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
namespace PoincareConjecture.RiemannianMetric
private theorem short_geodesic
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    (p : M) {r : ℝ} (hr : 0 < r) (x y : M)
    (hx : x ∈ g.ball p r) (hy : y ∈ g.ball p r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = x ∧ γ 1 = y ∧
      (g.edist x y).toReal ≤ 2 * r ∧ g.edist x y ≠ ⊤ ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.edist p (γ s) ≤ ENNReal.ofReal (3 * r) ∧
        g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) =
          (g.edist x y).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hxy : g.edist x y ≤ ENNReal.ofReal (2*r) := by
    calc
      _ ≤ g.edist x p + g.edist p y := edist_triangle x p y
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
        exact add_le_add (by rw [show g.edist x p = g.edist p x from edist_comm x p]; exact hx.le) hy.le
      _ = ENNReal.ofReal (2*r) := by rw [← ENNReal.ofReal_add hr.le (by positivity)]; congr 1; ring
  have hfin : g.edist x y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy
  have hlen : (g.edist x y).toReal ≤ 2*r :=
    (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hxy |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hcompact : IsCompact (closure (g.ball x (4*r))) :=
    (g.isCompact_closedBall_of_metricComplete hc x (4*r)).of_isClosed_subset
      isClosed_closure (closure_minimal (fun z hz => (show g.edist x z < ENNReal.ofReal (4*r) from hz).le)
        (isClosed_le (continuous_const.edist continuous_id) continuous_const))
  obtain ⟨ε,hε,γ,hγ,hγ0,hγ1,hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball x y (by positivity : 0 < 4*r)
      hcompact (hxy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
        (by linarith)))
  have hI : Icc (0:ℝ) 1 ⊆ Ioo (-ε) (1+ε) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have h0 := hI (show (0:ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C,hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at h0 x (by
    simpa only [hγ0] using mem_extChartAt_source x)).1
  have hC0 : g.tangentNorm x (deriv (fun s => extChartAt (𝓡 n) x (γ s)) 0) = C := by
    simpa only [RiemannianMetric.chartCoefficients_self, RiemannianMetric.tangentNorm] using
      (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
  have hCd : (C:ℝ) = (g.edist x y).toReal := by
    have he := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at he
    simpa only [ENNReal.toReal_ofReal C.coe_nonneg] using congrArg ENNReal.toReal he
  refine ⟨ε,hε,γ,hγ,hγ0,hγ1,hlen,hfin,fun s hs => ⟨?_,(hC s (hI hs)).trans hCd⟩⟩
  have hxs : g.edist x (γ s) ≤ g.edist x y := by
    have he := hmin 0 (by simp) s hs
    rw [hγ0,zero_sub,abs_neg,abs_of_nonneg hs.1] at he
    rw [he]
    exact mul_le_of_le_one_left' (by exact_mod_cast hs.2)
  calc
    _ ≤ g.edist p x + g.edist x (γ s) := edist_triangle p x (γ s)
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal (2*r) := add_le_add hx.le (hxs.trans hxy)
    _ = ENNReal.ofReal (3*r) := by rw [← ENNReal.ofReal_add hr.le (by positivity)]; congr 1; ring


theorem openFiber_zero_edist_eq_of_ambient_closedBall
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) {f : M → Fin 0 → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, Fin 0 → ℝ) ∞ f)
    (U : Opens M)
    (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ, Fin 0 → ℝ) f x))
    (c : Fin 0 → ℝ) (p : M) {r : ℝ} (hr : 0 < r)
    (hball : ∀ z, g.edist p z ≤ ENNReal.ofReal (3 * r) → z ∈ U) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n + 0) :=
      ⟨by simp⟩
    letI := openFiberChartedSpace (m := n) hf U hreg c
    letI := isManifold_openFiber (m := n) hf U hreg c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric (m := n) (k := 0) hf U hreg c
    ∀ x y : openFiber f U c, incl x ∈ g.ball p r → incl y ∈ g.ball p r →
      gL.edist x y = g.edist (incl x) (incl y) := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n + 0) := ⟨by simp⟩
  let := openFiberChartedSpace (m := n) hf U hreg c
  let := isManifold_openFiber (m := n) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric (m := n) (k := 0) hf U hreg c
  dsimp only
  intro x y hx hy
  have hincl := contMDiff_openFiberIncl (m := n) hf U hreg c
  have hnorm (z : openFiber f U c) (v : TangentSpace (𝓡 n) z) :
      gL.tangentNorm z v = g.tangentNorm (incl z) (mfderiv (𝓡 n) (𝓡 n) incl z v) :=
    g.openRegularFiberMetric_tangentNorm (m := n) (k := 0) hf U hreg c z v
  apply le_antisymm
  · obtain ⟨ε,hε,γ,hγ,hγ0,hγ1,_,hfin,hbounds⟩ := short_geodesic g hc p hr
      (incl x) (incl y) hx hy
    let I := Ioo (-ε) (1 + ε)
    have hγsmooth : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 n) ∞ γ I := fun s hs =>
      (PoincareConjecture.Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ hs).contMDiffWithinAt
    let J := I ∩ γ ⁻¹' (U : Set M)
    have hJo : IsOpen J := hγsmooth.continuousOn.isOpen_inter_preimage isOpen_Ioo U.isOpen
    have hsub : Icc (0 : ℝ) 1 ⊆ J := by
      intro s hs
      refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hball _ (hbounds s hs).1⟩
    let Γ : ℝ → openFiber f U c := fun s =>
      if hs : s ∈ J then ⟨⟨γ s, hs.2⟩, Subsingleton.elim _ _⟩ else x
    have heq (s : ℝ) (hs : s ∈ J) : incl (Γ s) = γ s := by
      simp only [Γ, dif_pos hs, incl, openFiberIncl]
    have hΓambient : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 n) ∞ (incl ∘ Γ) J :=
      (hγsmooth.mono inter_subset_left).congr heq
    have hΓ : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 n) ∞ Γ J :=
      (contMDiffOn_into_openFiber_iff (m := n) hf c U hreg Γ hJo).mpr hΓambient
    have hspeed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        gL.tangentNorm (Γ s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) Γ s 1) =
          (g.edist (incl x) (incl y)).toReal := by
      rw [hnorm]
      have hevent : incl ∘ Γ =ᶠ[𝓝 s] γ :=
        eventually_nhds_iff.mpr ⟨J,heq,hJo,hsub hs⟩
      have hcomp := mfderiv_comp s
        (hincl.mdifferentiable (by simp) (Γ s))
        ((hΓ.contMDiffAt (hJo.mem_nhds (hsub hs))).mdifferentiableAt (by simp))
      rw [← ContinuousLinearMap.comp_apply, ← hcomp, hevent.mfderiv_eq, heq s (hsub hs)]
      exact (hbounds s hs).2
    have hx0 : Γ 0 = x := by
      apply (isEmbedding_openFiberIncl f U c).injective
      exact (heq 0 (hsub (by simp))).trans hγ0
    have hy1 : Γ 1 = y := by
      apply (isEmbedding_openFiberIncl f U c).injective
      exact (heq 1 (hsub (by simp))).trans hγ1
    have hb := gL.edist_le_of_speed_le_on_Icc hJo hΓ
      (by norm_num : (0 : ℝ) ≤ 1) hsub (fun s hs => (hspeed s hs).le)
    simpa only [hx0,hy1,sub_zero,mul_one,ENNReal.ofReal_toReal hfin] using hb
  · have hb := gL.edist_le_mul_of_tangentNorm_mfderiv_le g
      (hincl.of_le (by simp)) (C := 1) (by norm_num)
      (fun z v => by rw [← hnorm]; simp) x y
    simpa only [ENNReal.ofReal_one, one_mul] using hb

end PoincareConjecture.RiemannianMetric
