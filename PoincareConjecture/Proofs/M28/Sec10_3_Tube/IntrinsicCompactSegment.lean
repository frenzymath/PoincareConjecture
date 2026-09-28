import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.IntrinsicMinimizer











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]




theorem exists_intrinsic_metric_segment_of_compact_sequence
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {p q : M} {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    {L : ℝ} {γ : ℕ → ℝ → M}
    (hγ : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (γ k) (Icc (0 : ℝ) 1))
    (h0 : ∀ k, γ k 0 = p) (h1 : ∀ k, γ k 1 = q)
    (hconf : ∀ k, MapsTo (γ k) (Icc (0 : ℝ) 1) K)
    (hbound : ∀ k, g.pathELength (γ k) 0 1 < ENNReal.ofReal L)
    (hlength : Tendsto (fun k => g.pathELength (γ k) 0 1) atTop
      (𝓝 (intrinsicEDist g (U : Set M) p q))) :
    ∃ η : ℝ → M, η 0 = p ∧ η 1 = q ∧
      ContinuousOn η (Icc (0 : ℝ) 1) ∧ MapsTo η (Icc (0 : ℝ) 1) K ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        intrinsicEDist g (U : Set M) (η s) (η t) =
          ENNReal.ofReal |s - t| * intrinsicEDist g (U : Set M) p q := by
  classical
  let gU := intrinsicOpenMetric g U
  let : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 3) U
  have hpK : p ∈ K := (h0 0) ▸ hconf 0 (by norm_num)
  have hqK : q ∈ K := (h1 0) ▸ hconf 0 (by norm_num)
  let pU : U := ⟨p, hKU hpK⟩
  let qU : U := ⟨q, hKU hqK⟩
  choose τ hτ heq hτlength using fun k =>
    exists_intrinsicOpenMetric_path_lift g U zero_le_one (hγ k)
      (fun t ht => hKU (hconf k ht))
  have hτ0 (k : ℕ) : τ k 0 = pU :=
    Subtype.ext ((heq k (by norm_num)).trans (h0 k))
  have hτ1 (k : ℕ) : τ k 1 = qU :=
    Subtype.ext ((heq k (by norm_num)).trans (h1 k))
  let K' : Set U := (Subtype.val : U → M) ⁻¹' K ∩
    {x | gU.edist pU x ≤ ENNReal.ofReal L}
  have hKpre : IsCompact ((Subtype.val : U → M) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
  have hK' : IsCompact K' := hKpre.inter_right
    (isClosed_le (continuous_const.edist continuous_id) continuous_const)
  have hτK (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : τ k t ∈ K' := by
    constructor
    · change (Subtype.val ∘ τ k) t ∈ K
      rw [heq k ht]
      exact hconf k ht
    · have hd := gU.edist_le_pathELength_of_mem_Icc (hτ k) ht
      rw [hτ0 k, hτlength k] at hd
      exact hd.trans (hbound k).le
  have hfinite (x y : K') : EDist.edist x y ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (edist_triangle x.1 pU y.1)
    apply ENNReal.add_ne_top.mpr
    constructor
    · rw [edist_comm]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top x.property.2
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top y.property.2
  let : MetricSpace K' := EMetricSpace.toMetricSpace hfinite
  let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  have hpK' : pU ∈ K' := (hτ0 0) ▸ hτK 0 (by norm_num)
  have hqK' : qU ∈ K' := (hτ1 0) ▸ hτK 0 (by norm_num)
  let pK : K' := ⟨pU, hpK'⟩
  let qK : K' := ⟨qU, hqK'⟩
  let σ (k : ℕ) (t : ℝ) : K' :=
    ⟨τ k (projIcc 0 1 zero_le_one t),
      hτK k (projIcc 0 1 zero_le_one t).property⟩
  have hσ (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      (σ k t).val = τ k t := by simp [σ, projIcc_of_mem zero_le_one ht]
  have hc (k : ℕ) : ContinuousOn (σ k) (Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    exact (hτ k).continuousOn.domRestrict.comp continuous_projIcc
  have hσ0 (k : ℕ) : σ k 0 = pK :=
    Subtype.ext ((hσ k (by norm_num)).trans (hτ0 k))
  have hσ1 (k : ℕ) : σ k 1 = qK :=
    Subtype.ext ((hσ k (by norm_num)).trans (hτ1 k))
  have hvar (k : ℕ) : eVariationOn (σ k) (Icc (0 : ℝ) 1) ≤
      g.pathELength (γ k) 0 1 := by
    rw [← hτlength k]
    apply gU.eVariationOn_le_pathELength_of_edist_le (hτ k)
    intro s hs t ht
    change gU.edist (σ k s).val (σ k t).val ≤ gU.edist (τ k s) (τ k t)
    rw [hσ k hs, hσ k ht]
  have hendpoint : EDist.edist pK qK = intrinsicEDist g (U : Set M) p q :=
    intrinsicOpenMetric_edist g U pU qU
  obtain ⟨η, hη0, hη1, _, hηdist⟩ :=
    Poincare.MetricCurves.exists_compact_metric_segment
      (K := (univ : Set K')) isCompact_univ hc hσ0 hσ1
      (fun _ _ _ => mem_univ _) hvar (by simpa only [hendpoint] using hlength)
  have hηcont : ContinuousOn η (Icc (0 : ℝ) 1) := by
    have hlip : LipschitzOnWith ⟨dist pK qK, dist_nonneg⟩ η (Icc (0 : ℝ) 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      rw [hηdist s hs t ht, Real.dist_eq]
      exact (mul_comm _ _).le
    exact hlip.continuousOn
  refine ⟨fun t => ((η t).val : M), congrArg (fun x : K' => (x.val : M)) hη0,
    congrArg (fun x : K' => (x.val : M)) hη1,
    continuous_subtype_val.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hηcont),
    fun t _ => (η t).property.1, ?_⟩
  intro s hs t ht
  rw [← intrinsicOpenMetric_edist g U (η s).val (η t).val]
  change EDist.edist (η s) (η t) = _
  rw [edist_dist, hηdist s hs t ht,
    ENNReal.ofReal_mul (abs_nonneg _), ← edist_dist, hendpoint]

end PoincareConjecture.M28
