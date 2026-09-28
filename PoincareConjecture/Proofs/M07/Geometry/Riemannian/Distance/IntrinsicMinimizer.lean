import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.PathVariation
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Curves.CompactMetricMinimizer

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_intrinsic_metric_segment_of_precompact_ball
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R) :
    ∃ η : ℝ → M, η 0 = p ∧ η 1 = q ∧
      MapsTo η (Icc (0 : ℝ) 1) (g.ball p R) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist p q := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨K, hK, hKR, γ, hγ, hlength⟩ :=
    g.exists_compact_confined_minimizing_sequence p q hR hcompact hq
  have hfinite (x y : K) : EDist.edist x y ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (edist_triangle x.1 p y.1)
    apply ENNReal.add_ne_top.mpr
    constructor
    · rw [edist_comm]
      exact ne_top_of_lt ((hKR x.property).trans_le le_top)
    · exact ne_top_of_lt ((hKR y.property).trans_le le_top)
  let : MetricSpace K := EMetricSpace.toMetricSpace hfinite
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hpK : p ∈ K := (hγ 0).1 ▸ (hγ 0).2.2.2 (by norm_num)
  have hqK : q ∈ K := (hγ 0).2.1 ▸ (hγ 0).2.2.2 (by norm_num)
  let pK : K := ⟨p, hpK⟩
  let qK : K := ⟨q, hqK⟩
  let σ (k : ℕ) (t : ℝ) : K :=
    ⟨γ k (projIcc 0 1 zero_le_one t),
      (hγ k).2.2.2 (projIcc 0 1 zero_le_one t).property⟩
  have hσ (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      (σ k t).val = γ k t := by simp [σ, projIcc_of_mem zero_le_one ht]
  have hc (k : ℕ) : ContinuousOn (σ k) (Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact (hγ k).2.2.1.continuousOn.domRestrict.comp continuous_projIcc
  have h0 (k : ℕ) : σ k 0 = pK := by
    apply Subtype.ext
    exact (hσ k (by norm_num)).trans (hγ k).1
  have h1 (k : ℕ) : σ k 1 = qK := by
    apply Subtype.ext
    exact (hσ k (by norm_num)).trans (hγ k).2.1
  have hbound (k : ℕ) : eVariationOn (σ k) (Icc (0 : ℝ) 1) ≤
      g.pathELength (γ k) 0 1 := by
    apply g.eVariationOn_le_pathELength_of_edist_le (hγ k).2.2.1
    intro s hs t ht
    change g.edist (σ k s).val (σ k t).val ≤ g.edist (γ k s) (γ k t)
    rw [hσ k hs, hσ k ht]
  obtain ⟨η, hη0, hη1, _, hηdist⟩ :=
    Poincare.MetricCurves.exists_compact_metric_segment
      (K := (univ : Set K)) isCompact_univ hc h0 h1
      (fun _ _ _ => mem_univ _) hbound hlength
  refine ⟨fun t => (η t).val, congrArg Subtype.val hη0,
    congrArg Subtype.val hη1, fun t _ => hKR (η t).property, ?_⟩
  · intro s hs t ht
    change EDist.edist (η s) (η t) =
      ENNReal.ofReal |s - t| * EDist.edist pK qK
    rw [edist_dist, hηdist s hs t ht,
      ENNReal.ofReal_mul (abs_nonneg _), edist_dist]

end PoincareConjecture.RiemannianMetric
