import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FrontierReplacement
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentLocality










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture





theorem m64Intrinsic_constrained_minimizer_metric_segment_of_frontier_connectors
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsClosed K) {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hconf : MapsTo gamma (Icc 0 L) K)
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma a → tau 1 = gamma b → MapsTo tau (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G tau 0 1)
    {u : ℝ} (hu : u ∈ Ioo 0 L) {O : Set AnnulusCoordinates}
    (hO : O ∈ 𝓝 (gamma u))
    (hside : ∀ p ∈ frontier K ∩ O, ∀ q ∈ frontier K ∩ O,
      ∃ g : ℝ → AnnulusCoordinates, ContinuousOn g (Icc 0 1) ∧
        g 0 = p ∧ g 1 = q ∧ MapsTo g (Icc 0 1) K ∧
        m64IntrinsicCurveVariation G g 0 1 ≤ G.edist p q) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ Icc (u - epsilon) (u + epsilon) ⊆ Icc 0 L ∧
      ∀ s ∈ Icc (u - epsilon) (u + epsilon),
        ∀ t ∈ Icc (u - epsilon) (u + epsilon),
          G.edist (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨⟨G.inner, G.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨V, hVnear, hVcompact, hVO⟩ :=
    exists_mem_nhds_isCompact_mapsTo continuous_id hO
  obtain ⟨c, hc, hcV⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 2) hVnear
  let R : ℝ := c
  have hR : 0 < R := by exact_mod_cast hc
  let epsilon := min (min (u / 2) ((L - u) / 2)) (R / 10)
  have hepsilon : 0 < epsilon :=
    lt_min (lt_min (half_pos hu.1) (half_pos (sub_pos.mpr hu.2))) (by positivity)
  have hepsu : epsilon ≤ u / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hepsL : epsilon ≤ (L - u) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hepsR : epsilon ≤ R / 10 := min_le_right _ _
  have hJ : Icc (u - epsilon) (u + epsilon) ⊆ Icc 0 L := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
  have hnear (s : ℝ) (hs : s ∈ Icc (u - epsilon) (u + epsilon)) :
      G.edist (gamma u) (gamma s) ≤ ENNReal.ofReal epsilon := by
    apply (hlip u ⟨hu.1.le, hu.2.le⟩ s (hJ hs)).trans
    exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hball (s : ℝ) (hs : s ∈ Icc (u - epsilon) (u + epsilon)) :
      G.ball (gamma s) (R / 2) ⊆ V := by
    intro z hz
    apply hcV
    have hdist : G.edist (gamma u) z < ENNReal.ofReal R := calc
      G.edist (gamma u) z ≤ G.edist (gamma u) (gamma s) + G.edist (gamma s) z :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal epsilon + G.edist (gamma s) z := add_le_add (hnear s hs) le_rfl
      _ < ENNReal.ofReal epsilon + ENNReal.ofReal (R / 2) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hz
      _ = ENNReal.ofReal (epsilon + R / 2) :=
        (ENNReal.ofReal_add hepsilon.le (half_pos hR).le).symm
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)
    change G.edist (gamma u) z < (c : ℝ≥0∞)
    simpa only [R, ENNReal.ofReal_coe_nnreal] using hdist
  refine ⟨epsilon, hepsilon, hJ, ?_⟩
  intro s hs t ht
  wlog hst : s ≤ t generalizing s t
  · have hcomm : G.edist (gamma s) (gamma t) = G.edist (gamma t) (gamma s) :=
      Manifold.riemannianEDist_comm
    rw [hcomm, abs_sub_comm]
    exact this t ht s hs (le_of_not_ge hst)
  apply le_antisymm (hlip s (hJ hs) t (hJ ht))
  have hcompact : IsCompact (closure (G.ball (gamma s) (R / 2))) :=
    hVcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (hball s hs) hVcompact.isClosed)
  have htball : gamma t ∈ G.ball (gamma s) (R / 2) := by
    apply (hlip s (hJ hs) t (hJ ht)).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (half_pos hR)).mpr
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    linarith [hs.1, ht.2]
  obtain ⟨eta, heta0, heta1, hetaball, hetadist⟩ :=
    G.exists_intrinsic_metric_segment_of_precompact_ball (gamma s) (gamma t)
      (half_pos hR) hcompact htball
  have hetac := G.continuousOn_of_edist_segment (G.edist_ne_top _ _) hetadist
  obtain ⟨tau, htauc, htau0, htau1, htauconf, htauvar⟩ :=
    m64Intrinsic_exists_confined_competitor_of_frontier_segments G hK hetac
      (by simpa only [heta0] using hconf (hJ hs))
      (by simpa only [heta1] using hconf (hJ ht))
      (fun x hx => hVO (hball s hs (hetaball hx)))
      (C := (G.edist (gamma s) (gamma t)).toReal) ENNReal.toReal_nonneg (by
        intro x hx y hy
        rw [hetadist x hx y hy, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (G.edist_ne_top _ _), mul_comm]) hside
  have h := (hmin s (hJ hs) t (hJ ht) hst tau htauc
    (htau0.trans heta0) (htau1.trans heta1) htauconf).trans htauvar
  simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub,
    ENNReal.ofReal_toReal (G.edist_ne_top _ _)] using h

end PoincareConjecture
