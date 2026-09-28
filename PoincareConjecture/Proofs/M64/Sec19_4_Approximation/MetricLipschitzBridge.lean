import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M60.Mathlib.CompactExtendedLipschitz
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64AnnulusDomain_convex : Convex ℝ m64AnnulusDomain := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ (a • x + b • y) 0 ∧ (a • x + b • y) 0 ≤ curvePeriod ∧
    0 ≤ (a • x + b • y) 1 ∧ (a • x + b • y) 1 ≤ 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · constructor
    · calc
        a * x 0 + b * y 0 ≤ a * curvePeriod + b * curvePeriod :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
            (mul_le_mul_of_nonneg_left hy.2.1 hb)
        _ = curvePeriod := by rw [← add_mul, hab, one_mul]
    · constructor
      · exact add_nonneg (mul_nonneg ha hx.2.2.1) (mul_nonneg hb hy.2.2.1)
      · calc
          a * x 1 + b * y 1 ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx.2.2.2 ha)
              (mul_le_mul_of_nonneg_left hy.2.2.2 hb)
          _ = 1 := by rw [← add_mul, hab, one_mul]






theorem m64_lipschitzOn_nhds_of_contMDiffAt
    (g : RiemannianMetric n M) {f : LoopPlane → M} {x : LoopPlane}
    (hf : ContMDiffAt (𝓡 2) (𝓡 n) 1 f x) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
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
  obtain ⟨R, hR, _hRtarget, hInv, _hForward⟩ :=
    M40.normalizedSmoothChart_exists_lipschitz_ball e he hx
      contMDiffOn_chart contMDiffOn_chart_symm 2 (by norm_num)
  have hchiAt :=
    (M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart).contMDiffAt
      (chi.open_source.mem_nhds hchi)
  have hcoord : ContMDiffAt (𝓡 2) 𝓘(ℝ, TangentSpace (𝓡 n) (f x)) 1
      (chi ∘ f) x := by
    exact (hchiAt.of_le (m := 1) (by norm_num)).comp x hf
  obtain ⟨K, _hK, U, hU, hcoordLip⟩ :=
    M40.exists_lipschitzOn_nhds_of_contMDiffAt hcoord
  have hU' : U ∩ f ⁻¹' chi.source ∩
      (chi ∘ f) ⁻¹' Metric.ball (chi (f x)) R ∈ 𝓝 x := by
    apply inter_mem (inter_mem hU
      (hf.continuousAt.preimage_mem_nhds (chi.open_source.mem_nhds hchi)))
    exact (hcoord.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hR))
  let V := U ∩ f ⁻¹' chi.source ∩
      (chi ∘ f) ⁻¹' Metric.ball (chi (f x)) R
  have hcoordV : LipschitzOnWith K (chi ∘ f) V := hcoordLip.mono (by
    intro y hy
    exact hy.1.1)
  have hmap : MapsTo (chi ∘ f) V (Metric.ball (chi (f x)) R) := by
    intro y hy
    exact hy.2
  have hcomp : LipschitzOnWith (2 * K) (chi.symm ∘ (chi ∘ f)) V :=
    hInv.comp hcoordV hmap
  refine ⟨2 * K, V, hU', ?_⟩
  intro y hy z hz
  have hy' : f y ∈ chi.source := hy.1.2
  have hz' : f z ∈ chi.source := hz.1.2
  have heqy : chi.symm (chi (f y)) = f y := chi.left_inv hy'
  have heqz : chi.symm (chi (f z)) = f z := chi.left_inv hz'
  have hc := hcomp hy hz
  change g.edist (chi.symm (chi (f y))) (chi.symm (chi (f z))) ≤
    ((2 * K : ℝ≥0) : ℝ≥0∞) * edist y z at hc
  simpa only [heqy, heqz, edist_dist, dist_eq_norm] using hc





theorem m64_lipschitzOn_nhds_of_contMDiffOn
    (g : RiemannianMetric n M) {f : LoopPlane → M} {S : Set LoopPlane}
    (hS : IsOpen S) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f S) :
    ∀ x ∈ S, ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      g.edist (f y) (f z) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  intro x hx
  exact m64_lipschitzOn_nhds_of_contMDiffAt g
    ((hf x hx).contMDiffAt (hS.mem_nhds hx))








theorem m64AnnulusDomain_edist_ne_top
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    (hcontinuous : ContinuousOn f m64AnnulusDomain) :
    ∀ x ∈ m64AnnulusDomain, ∀ y ∈ m64AnnulusDomain,
      g.edist (f x) (f y) ≠ (⊤ : ENNReal) := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let R := f '' m64AnnulusDomain
  have hR : IsPreconnected R :=
    m64AnnulusDomain_convex.isPreconnected.image f hcontinuous
  let : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp hR
  intro x hx y hy
  exact Poincare.edist_ne_top_of_preconnected
    (⟨f x, mem_image_of_mem f hx⟩ : R)
    (⟨f y, mem_image_of_mem f hy⟩ : R)




theorem m64Annulus_hLip_of_local
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hLocal : ∀ x ∈ m64AnnulusDomain, ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ z ∈ U,
        g.edist (f y) (f z) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖) :
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
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  have hloc : LocallyLipschitzOn m64AnnulusDomain f := by
    intro x hx
    obtain ⟨K, U, hU, hK⟩ := hLocal x hx
    refine ⟨K, U ∩ m64AnnulusDomain,
      inter_mem (nhdsWithin_le_nhds hU) self_mem_nhdsWithin, ?_⟩
    intro y hy z hz
    change g.edist (f y) (f z) ≤ (K : ℝ≥0∞) * edist y z
    simpa only [edist_dist, dist_eq_norm] using hK y hy.1 z hz.1
  obtain ⟨K, hK⟩ := M60.exists_lipschitzOnWith_of_compact_edist_ne_top
    m64AnnulusDomain_isCompact hloc
      (m64AnnulusDomain_edist_ne_top g hcontinuous)
  refine ⟨K, ?_⟩
  intro x y
  have h := hK x.property y.property
  change g.edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist (x : LoopPlane) y at h
  simpa only [edist_dist, dist_eq_norm] using h

end PoincareConjecture
