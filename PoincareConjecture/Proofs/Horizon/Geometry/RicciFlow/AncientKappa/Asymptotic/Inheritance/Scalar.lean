import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem bilinear_eq_of_basis {n : ℕ}
    {B B' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (h : ∀ a b : Fin n, B (EuclideanSpace.basisFun (Fin n) ℝ a)
      (EuclideanSpace.basisFun (Fin n) ℝ b) =
        B' (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) :
    B = B' := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro a
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  exact h a

theorem FlowCarrier.scalarCurvature_eq_of_coordinate_germ
    {n : ℕ} (C : FlowCarrier n) (gM : C.metric) (DM : LeviCivitaData gM)
    (q : C.carrier) (t : ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp : p ∈ (extChartAt (𝓡 n) q).target)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      C.coordinateCoefficient q (fun _ y v w ↦ gM.inner y v w) a b (t, x)) :
    DE.scalarCurvature p = DM.scalarCurvature ((extChartAt (𝓡 n) q).symm p) := by
  let c := extChartAt (𝓡 n) q
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (inter_mem (extChartAt_target_mem_nhds' hp) h)
  apply DE.scalarCurvature_eq_of_local_isometry DM hVo
    (fun x hx ↦ (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
      (hV hx).1).contMDiffAt (extChartAt_target_mem_nhds' (hV hx).1)
        |>.contMDiffWithinAt) (x := p) (hx := hpV)
  intro x hx
  have hB : gE.euclideanCoefficients x = gM.pullbackCoefficients c.symm x :=
    bilinear_eq_of_basis (hV hx).2
  exact fun u v ↦ congrArg (fun B ↦ B u v) hB

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {tau : ℝ} {R : AncientRescaling K tau}

theorem AncientSpacetimeEmbedding.scalarCurvature_eq_of_coordinate_germ
    {L : AncientLimitFlow n} {J : Set ℝ} {U : Set L.carrier.carrier}
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U)) (hU : IsOpen U)
    (q : L.carrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : J ∈ 𝓝 p.1)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p.2, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) = ancientPullbackCoefficient e q a b (p.1, x)) :
    DE.scalarCurvature p.2 = (R.flow.connection p.1).scalarCurvature
      ((e.toFun (p.1, (extChartAt (𝓡 n) q).symm p.2)).2) := by
  let c := extChartAt (𝓡 n) q
  let f : L.carrier.carrier → M := fun y ↦ (e.toFun (p.1, y)).2
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU
  have hc (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx.1).contMDiffAt
      (extChartAt_target_mem_nhds' hx.1)
  have hf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (c.symm x) :=
    e.spatialMap_contMDiffAt_of_time_nhds hU ht hx.2
  have hd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ W) :
      mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x =
        (mfderiv (𝓡 n) (𝓡 n) f (c.symm x)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm x) :=
    mfderiv_comp x ((hf x hx).mdifferentiableAt (by simp))
      ((hc x hx).mdifferentiableAt (by simp))
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (inter_mem (hW.mem_nhds hp) h)
  apply DE.scalarCurvature_eq_of_local_isometry (R.flow.connection p.1) hVo
    (fun x hx ↦ ((hf x (hV hx).1).comp x (hc x (hV hx).1)).contMDiffWithinAt)
    (x := p.2) (hx := hpV)
  intro x hx
  have hB : gE.euclideanCoefficients x =
      (R.flow.metric p.1).pullbackCoefficients (f ∘ c.symm) x := by
    apply bilinear_eq_of_basis
    intro a b
    rw [(hV hx).2 a b]
    change _ = (R.flow.metric p.1).inner (f (c.symm x))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) x (EuclideanSpace.basisFun (Fin n) ℝ b))
    rw [hd x (hV hx).1]
    rfl
  exact fun u v ↦ congrArg (fun B ↦ B u v) hB

namespace AncientCompactTimeConvergence

variable {S : AncientRescalingSequence K} (G : AncientCompactTimeConvergence S)

theorem tendsto_scalarCurvature (t : ℝ) (ht : t < 0) (x : G.limit.carrier.carrier) :
    Tendsto (fun k ↦ ((S.rescaling (G.subsequence k)).flow.connection t).scalarCurvature
      ((G.embedding k).toFun (t, x)).2) atTop
      (𝓝 ((G.limit.flow.connection t).scalarCurvature x)) := by
  classical
  let c := extChartAt (𝓡 n) x
  let p := c x
  have hp : p ∈ c.target := c.map_source (mem_extChartAt_source x)
  have hcx : (extChartAt (𝓡 n) x).symm p = x := c.left_inv (mem_extChartAt_source x)
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limit.carrier.exists_local_coordinate_realization
    (G.limit.flow.metric t) x t p hp
  have hg : ∀ᶠ y in 𝓝 p, ∀ a b : Fin n,
      g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      G.limit.carrier.coordinateCoefficient x
        (fun _ y v w ↦ (G.limit.flow.metric t).inner y v w) a b (t, y) :=
    Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData g,
        ∀ᶠ y in 𝓝 p, ∀ a b : Fin n,
          gd.1.euclideanCoefficients y (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b) =
          ancientPullbackCoefficient (G.embedding k) x a b (t, y) := by
    filter_upwards [eventually_timeWindow_mem_nhds ht, G.eventually_mem_exhaustion x]
      with k hkt hkx
    obtain ⟨gk, Dk, hk⟩ := (G.embedding k).exists_local_coordinate_realization
      (G.exhaustion_open k) x (t, p) hkt ⟨hp, by simpa only [hcx] using hkx⟩
    exact ⟨⟨gk, Dk⟩, hk⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hscalar := LeviCivitaData.tendsto_scalarCurvature_of_scalar_metric_jets
    (l := atTop) (fun k ↦ (gd k).2) D p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      erw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p g hg r a b]
      apply (G.tendsto_coordinate_spatial_metricJet x r a b (t, p) ht hp).congr'
      filter_upwards [hgd] with k hk
      exact (G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x (ancientPullbackInnerValue (G.embedding k)) t p (gd k).1 hk r a b).symm)
  have hlim : D.scalarCurvature p = (G.limit.flow.connection t).scalarCurvature x := by
    simpa only [hcx] using G.limit.carrier.scalarCurvature_eq_of_coordinate_germ
      (G.limit.flow.metric t) (G.limit.flow.connection t) x t p hp g D hg
  rw [hlim] at hscalar
  apply hscalar.congr'
  filter_upwards [hgd, eventually_timeWindow_mem_nhds ht, G.eventually_mem_exhaustion x]
    with k hk hkt hkx
  simpa only [hcx] using (G.embedding k).scalarCurvature_eq_of_coordinate_germ
    (G.exhaustion_open k) x (t, p) hkt ⟨hp, by simpa only [hcx] using hkx⟩
      (gd k).1 (gd k).2 hk

theorem scalar_monotone (P : AncientAsymptoticSolitonPredecessors K)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 0) (x : G.limit.carrier.carrier) :
    (G.limit.flow.connection s).scalarCurvature x ≤
      (G.limit.flow.connection t).scalarCurvature x := by
  obtain ⟨H⟩ := P.structural
  apply le_of_tendsto_of_tendsto (G.tendsto_scalarCurvature s (lt_of_le_of_lt hst ht) x)
    (G.tendsto_scalarCurvature t ht x)
  filter_upwards [eventually_timeWindow_mem_nhds (lt_of_le_of_lt hst ht),
    eventually_timeWindow_mem_nhds ht, G.eventually_mem_exhaustion x] with k hks hkt hkx
  rw [(S.rescaling (G.subsequence k)).scalar_scale s (lt_of_le_of_lt hst ht),
    (S.rescaling (G.subsequence k)).scalar_scale t ht,
    G.spatial_time_independent k s t x (mem_of_mem_nhds hks) (mem_of_mem_nhds hkt) hkx]
  exact mul_le_mul_of_nonneg_left ((H.structural M K).scalar_monotone _ _
    (mul_le_mul_of_nonneg_left hst (S.scale_pos _).le)
    (mul_nonpos_of_nonneg_of_nonpos (S.scale_pos _).le ht.le) _)
    (S.scale_pos _).le

theorem scalar_derivative_nonnegative (P : AncientAsymptoticSolitonPredecessors K)
    (t : ℝ) (ht : t < 0) (x : G.limit.carrier.carrier) :
    ∃ dR : ℝ, HasDerivWithinAt
      (fun s ↦ (G.limit.flow.connection s).scalarCurvature x) dR (Iio 0) t ∧ 0 ≤ dR := by
  have hd : DifferentiableWithinAt ℝ
      (fun s ↦ (G.limit.flow.connection s).scalarCurvature x) (Iio 0) t :=
    (G.limit.flow.hasDerivAt_scalarCurvature
    (show t ∈ interior (Iio 0) by simpa only [interior_Iio, mem_Iio] using ht)
    x).differentiableAt.differentiableWithinAt
  refine ⟨_, hd.hasDerivWithinAt, MonotoneOn.derivWithin_nonneg ?_⟩
  intro s hs u hu hsu
  exact G.scalar_monotone P hsu hu x

end AncientCompactTimeConvergence
end PoincareConjecture
