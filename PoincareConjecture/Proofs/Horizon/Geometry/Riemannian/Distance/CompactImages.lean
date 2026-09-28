import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactMetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

theorem exists_uniform_image_distance_bound_of_chart_convergence
    {m n : ℕ} {S Q : Type*} {M : ℕ → Type*}
    [TopologicalSpace S] [T3Space S] [CompactSpace S] [ConnectedSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) S] [IsManifold (𝓡 m) ∞ S]
    [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (gS : RiemannianMetric m S) (g : RiemannianMetric n Q)
    (gseq : ℕ → RiemannianMetric n Q) (gM : ∀ k, RiemannianMetric n (M k))
    {b : S → Q} (hb : ContMDiff (𝓡 m) (𝓡 n) ∞ b)
    (hbmetric : ∀ x v w, gS.inner x v w = g.inner (b x)
      (mfderiv (𝓡 m) (𝓡 n) b x v) (mfderiv (𝓡 m) (𝓡 n) b x w))
    {A : ∀ k, Q → M k}
    (hA : ∀ᶠ k in atTop, ContMDiff (𝓡 n) (𝓡 n) ∞ (A k))
    (hmetric : ∀ᶠ k in atTop, ∀ q v w, (gseq k).inner q v w =
      (gM k).inner (A k q) (mfderiv (𝓡 n) (𝓡 n) (A k) q v)
        (mfderiv (𝓡 n) (𝓡 n) (A k) q w))
    (hcharts : ∀ p ∈ range b,
      ∃ c : OpenPartialHomeomorph Q (EuclideanSpace ℝ (Fin n)),
        p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
        ∀ C, IsCompact C → C ⊆ c.target →
          TendstoUniformlyOn (fun k => (gseq k).pullbackCoefficients c.symm)
            (g.pullbackCoefficients c.symm) atTop C) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in atTop, ∀ x y : S,
      ((gM k).edist (A k (b x)) (A k (b y))).toReal ≤ D := by
  let := gS.toMetricSpace
  obtain ⟨d, hd⟩ := Metric.isBounded_iff.mp
    (isCompact_univ : IsCompact (univ : Set S)).isBounded
  refine ⟨2 * (|d| + 1), by positivity, ?_⟩
  have hbound := eventually_inner_le_twice_of_chart_convergence gseq g
    (isCompact_range hb.continuous) hcharts
  filter_upwards [hA, hmetric, hbound] with k hkA hkm hkb x y
  have hdiff := hkA.comp hb
  have hle : (gM k).edist (A k (b x)) (A k (b y)) ≤
      ENNReal.ofReal 2 * gS.edist x y := by
    apply gS.edist_le_mul_of_inner_mfderiv_le (gM k)
      (hdiff.of_le (by simp)) (by norm_num : (0 : ℝ) < 2)
    intro z v
    rw [mfderiv_comp z (hkA.mdifferentiable (by simp) (b z))
      (hb.mdifferentiable (by simp) z)]
    change (gM k).inner (A k (b z))
      (mfderiv (𝓡 n) (𝓡 n) (A k) (b z) (mfderiv (𝓡 m) (𝓡 n) b z v))
      (mfderiv (𝓡 n) (𝓡 n) (A k) (b z) (mfderiv (𝓡 m) (𝓡 n) b z v)) ≤ _
    rw [← hkm]
    have hh := hkb (b z) (mem_range_self z) (mfderiv (𝓡 m) (𝓡 n) b z v)
    rw [← hbmetric] at hh
    have hnonneg : 0 ≤ gS.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (gS.pos z v hv).le
    nlinarith
  have hre := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gS.edist_ne_top x y)) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at hre
  have hdist : (gS.edist x y).toReal ≤ d := hd (mem_univ x) (mem_univ y)
  nlinarith [le_abs_self d]

end PoincareConjecture.RiemannianMetric
