import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import Mathlib.Analysis.Calculus.ContDiff.RCLike





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m64_lipschitzOn_nhdsWithin_of_contMDiffWithinAt
    (g : RiemannianMetric n M) {f : LoopPlane → M} {S : Set LoopPlane}
    {x : LoopPlane} (hS : Convex ℝ S)
    (hf : ContMDiffWithinAt (𝓡 2) (𝓡 n) 1 f S x) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝[S] x, ∀ y ∈ U, ∀ z ∈ U,
      g.edist (f y) (f z) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  have he : e.MDifferentiable (𝓡 n) (𝓡 n) := mdifferentiable_chart _
  have hx : f x ∈ e.source := mem_chart_source _ _
  let chi := M40.normalizedSmoothChart e he hx
  have hchi : f x ∈ chi.source := by
    simpa only [chi, M40.normalizedSmoothChart_source] using hx
  obtain ⟨R, hR, -, hInv, -⟩ :=
    M40.normalizedSmoothChart_exists_lipschitz_ball e he hx
      contMDiffOn_chart contMDiffOn_chart_symm 2 (by norm_num)
  have hchiAt :=
    (M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart).contMDiffAt
      (chi.open_source.mem_nhds hchi)
  have hcoord : ContMDiffWithinAt (𝓡 2) 𝓘(ℝ, TangentSpace (𝓡 n) (f x)) 1
      (chi ∘ f) S x := (hchiAt.of_le (m := 1) (by norm_num)).comp_contMDiffWithinAt x hf
  obtain ⟨K, U, hU, hcoordLip⟩ := hcoord.contDiffWithinAt.exists_lipschitzOnWith hS
  let V := U ∩ f ⁻¹' chi.source ∩ (chi ∘ f) ⁻¹' Metric.ball (chi (f x)) R
  have hV : V ∈ 𝓝[S] x := inter_mem (inter_mem hU
    (hf.continuousWithinAt.preimage_mem_nhdsWithin (chi.open_source.mem_nhds hchi)))
      (hcoord.continuousWithinAt.preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ hR))
  have hcoordV : LipschitzOnWith K (chi ∘ f) V :=
    hcoordLip.mono fun _ hy => hy.1.1
  have hm : MapsTo (chi ∘ f) V (Metric.ball (chi (f x)) R) := fun _ hy => hy.2
  have hcomp : LipschitzOnWith (2 * K) (chi.symm ∘ (chi ∘ f)) V :=
    hInv.comp hcoordV hm
  refine ⟨2 * K, V, hV, ?_⟩
  intro y hy z hz
  have heqy : chi.symm (chi (f y)) = f y := chi.left_inv hy.1.2
  have heqz : chi.symm (chi (f z)) = f z := chi.left_inv hz.1.2
  have hc := hcomp hy hz
  change g.edist (chi.symm (chi (f y))) (chi.symm (chi (f z))) ≤
    ((2 * K : ℝ≥0) : ℝ≥0∞) * edist y z at hc
  simpa only [heqy, heqz, edist_dist, dist_eq_norm] using hc




theorem m64Annulus_hLip_of_contMDiffOn
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain) :
    ∃ K : ℝ≥0, ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hloc : LocallyLipschitzOn m64AnnulusDomain f := by
    intro x hx
    obtain ⟨K, U, hU, hK⟩ := m64_lipschitzOn_nhdsWithin_of_contMDiffWithinAt g
      m64AnnulusDomain_convex (hf x hx)
    refine ⟨K, U, hU, ?_⟩
    intro y hy z hz
    change g.edist (f y) (f z) ≤ (K : ℝ≥0∞) * edist y z
    simpa only [edist_dist, dist_eq_norm] using hK y hy z hz
  obtain ⟨K, hK⟩ := M60.exists_lipschitzOnWith_of_compact_edist_ne_top
    m64AnnulusDomain_isCompact hloc
      (m64AnnulusDomain_edist_ne_top g hf.continuousOn)
  refine ⟨K, ?_⟩
  intro x y
  have h := hK x.property y.property
  change g.edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist (x : LoopPlane) y at h
  simpa only [edist_dist, dist_eq_norm] using h

end PoincareConjecture
