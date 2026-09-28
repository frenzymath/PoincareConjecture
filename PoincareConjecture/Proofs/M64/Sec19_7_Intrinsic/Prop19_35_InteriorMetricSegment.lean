import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionMinimizer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentLocality














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture






theorem m64Intrinsic_constrained_minimizer_local_metric_segment
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {γ : ℝ → AnnulusCoordinates} {L : ℝ}
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (γ s) (γ t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ τ : ℝ → AnnulusCoordinates, ContinuousOn τ (Icc 0 1) →
        τ 0 = γ a → τ 1 = γ b → MapsTo τ (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G τ 0 1)
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hinterior : γ u ∈ interior K) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ Icc (u - epsilon) (u + epsilon) ⊆ Icc 0 L ∧
      ∀ s ∈ Icc (u - epsilon) (u + epsilon),
        ∀ t ∈ Icc (u - epsilon) (u + epsilon),
          G.edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨⟨G.inner, G.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨c, hc, hcK⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 2)
    (mem_interior_iff_mem_nhds.mp hinterior)
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
      G.edist (γ u) (γ s) ≤ ENNReal.ofReal epsilon := by
    apply (hlip u ⟨hu.1.le, hu.2.le⟩ s (hJ hs)).trans
    exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hball (s : ℝ) (hs : s ∈ Icc (u - epsilon) (u + epsilon)) :
      G.ball (γ s) (R / 2) ⊆ K := by
    intro z hz
    apply hcK
    have hdist : G.edist (γ u) z < ENNReal.ofReal R := calc
      G.edist (γ u) z ≤ G.edist (γ u) (γ s) + G.edist (γ s) z :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal epsilon + G.edist (γ s) z := add_le_add (hnear s hs) le_rfl
      _ < ENNReal.ofReal epsilon + ENNReal.ofReal (R / 2) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hz
      _ = ENNReal.ofReal (epsilon + R / 2) :=
        (ENNReal.ofReal_add hepsilon.le (half_pos hR).le).symm
      _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)
    change G.edist (γ u) z < (c : ℝ≥0∞)
    simpa only [R, ENNReal.ofReal_coe_nnreal] using hdist
  refine ⟨epsilon, hepsilon, hJ, ?_⟩
  intro s hs t ht
  wlog hst : s ≤ t generalizing s t
  · have hcomm : G.edist (γ s) (γ t) = G.edist (γ t) (γ s) :=
      Manifold.riemannianEDist_comm
    rw [hcomm, abs_sub_comm]
    exact this t ht s hs (le_of_not_ge hst)
  apply le_antisymm (hlip s (hJ hs) t (hJ ht))
  have hcompact : IsCompact (closure (G.ball (γ s) (R / 2))) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal (hball s hs) hK.isClosed)
  have htball : γ t ∈ G.ball (γ s) (R / 2) := by
    apply (hlip s (hJ hs) t (hJ ht)).trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (half_pos hR)).mpr
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    linarith [hs.1, ht.2]
  obtain ⟨η, hη0, hη1, hηball, hηdist⟩ :=
    G.exists_intrinsic_metric_segment_of_precompact_ball (γ s) (γ t)
      (half_pos hR) hcompact htball
  have hηc := G.continuousOn_of_edist_segment (G.edist_ne_top (γ s) (γ t)) hηdist
  have hηvar : m64IntrinsicCurveVariation G η 0 1 ≤ G.edist (γ s) (γ t) := by
    have h := m64Intrinsic_curveVariation_le_of_edist_le G
      (C := (G.edist (γ s) (γ t)).toReal) ENNReal.toReal_nonneg (by
        intro a ha b hb
        rw [hηdist a ha b hb, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (G.edist_ne_top (γ s) (γ t)), mul_comm])
    simpa only [ENNReal.ofReal_toReal (G.edist_ne_top (γ s) (γ t))] using h
  have h := (hmin s (hJ hs) t (hJ ht) hst η hηc hη0 hη1
    (fun a ha => hball s hs (hηball ha))).trans hηvar
  simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using h

end PoincareConjecture
