import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConstrainedMinimizer
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcReplacement
import PoincareConjecture.Proofs.M64.Mathlib.VariationConcatenation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.PathVariation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture

@[instance_reducible] private def intrinsicDistanceMetric
    (G : RiemannianMetric 2 AnnulusCoordinates) : MetricSpace AnnulusCoordinates := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨⟨G.inner, G.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace AnnulusCoordinates :=
    EMetricSpace.ofRiemannianMetric (𝓡 2) AnnulusCoordinates
  exact EMetricSpace.toMetricSpace (fun x y => G.edist_ne_top x y)

def m64IntrinsicCurveVariation (G : RiemannianMetric 2 AnnulusCoordinates)
    (γ : ℝ → AnnulusCoordinates) (a b : ℝ) : ℝ≥0∞ :=
  @eVariationOn ℝ _ AnnulusCoordinates
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace γ (Icc a b)

theorem m64Intrinsic_curveVariation_affine
    (G : RiemannianMetric 2 AnnulusCoordinates) (γ : ℝ → AnnulusCoordinates) (a b : ℝ) :
    m64IntrinsicCurveVariation G (fun t => γ (a + (b - a) * t)) 0 1 =
      m64IntrinsicCurveVariation G γ (min a b) (max a b) := by
  let : MetricSpace AnnulusCoordinates := intrinsicDistanceMetric G
  let : PseudoEMetricSpace AnnulusCoordinates :=
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace
  let f := fun t : ℝ => a + (b - a) * t
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hf0 : f 0 = a := by simp [f]
  have hf1 : f 1 = b := by simp [f]
  change eVariationOn (γ ∘ f) (Icc (0 : ℝ) 1) = eVariationOn γ (Icc (min a b) (max a b))
  rcases le_total a b with hab | hba
  · have hmono : MonotoneOn f (Icc 0 1) := by
      intro x _ y _ hxy
      dsimp only [f]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hab))
    rw [eVariationOn.comp_eq_of_monotoneOn γ f hmono,
      hf.continuousOn.image_Icc_of_monotoneOn zero_le_one hmono, hf0, hf1,
      min_eq_left hab, max_eq_right hab]
  · have hanti : AntitoneOn f (Icc 0 1) := by
      intro x _ y _ hxy
      dsimp only [f]
      exact add_le_add le_rfl (mul_le_mul_of_nonpos_left hxy (sub_nonpos.mpr hba))
    rw [eVariationOn.comp_eq_of_antitoneOn γ f hanti,
      hf.continuousOn.image_Icc_of_antitoneOn zero_le_one hanti, hf0, hf1,
      min_eq_right hba, max_eq_left hba]

theorem m64Intrinsic_exists_join_with_variation
    (G : RiemannianMetric 2 AnnulusCoordinates) {f g : ℝ → AnnulusCoordinates}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hjoin : f 1 = g 0) :
    ∃ q : ℝ → AnnulusCoordinates, ContinuousOn q (Icc 0 1) ∧ q 0 = f 0 ∧ q 1 = g 1 ∧
      (∀ t ∈ Icc 0 1, q t ∈ f '' Icc 0 1 ∪ g '' Icc 0 1) ∧
      m64IntrinsicCurveVariation G q 0 1 =
        m64IntrinsicCurveVariation G f 0 1 + m64IntrinsicCurveVariation G g 0 1 := by
  let : MetricSpace AnnulusCoordinates := intrinsicDistanceMetric G
  let : PseudoEMetricSpace AnnulusCoordinates :=
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace
  exact m64_exists_join_with_variation hf hg hjoin

theorem m64Intrinsic_curveVariation_le_pathELength
    (G : RiemannianMetric 2 AnnulusCoordinates) {γ : ℝ → AnnulusCoordinates}
    {a b : ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 γ (Icc a b)) :
    m64IntrinsicCurveVariation G γ a b ≤ G.pathELength γ a b := by
  let : MetricSpace AnnulusCoordinates := intrinsicDistanceMetric G
  let : PseudoEMetricSpace AnnulusCoordinates :=
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace
  exact G.eVariationOn_le_pathELength_of_edist_le hγ (fun _ _ _ _ => le_rfl)

theorem m64Intrinsic_curveVariation_le_of_edist_le
    (G : RiemannianMetric 2 AnnulusCoordinates) {γ : ℝ → AnnulusCoordinates}
    {C : ℝ} (hC : 0 ≤ C)
    (hγ : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      G.edist (γ s) (γ t) ≤ ENNReal.ofReal (C * |s - t|)) :
    m64IntrinsicCurveVariation G γ 0 1 ≤ ENNReal.ofReal C := by
  let : MetricSpace AnnulusCoordinates := intrinsicDistanceMetric G
  let : PseudoEMetricSpace AnnulusCoordinates :=
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace
  have hlip : LipschitzOnWith ⟨C, hC⟩ γ (Icc 0 1) := by
    intro s hs t ht
    change G.edist (γ s) (γ t) ≤ ENNReal.ofNNReal (NNReal.mk C hC) * edist s t
    have h := hγ s hs t ht
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_eq_coe_nnreal hC] at h
    simpa only [edist_dist, Real.dist_eq] using h
  rw [ENNReal.ofReal_eq_coe_nnreal hC]
  exact Poincare.MetricCurves.eVariationOn_le_of_lipschitzOnWith hlip

theorem m64Intrinsic_exists_compact_region_shortest_curve
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {p q : AnnulusCoordinates} {σ : ℝ → AnnulusCoordinates}
    (hc : ContinuousOn σ (Icc 0 1)) (h0 : σ 0 = p) (h1 : σ 1 = q)
    (hconf : MapsTo σ (Icc 0 1) K) {B : ℝ}
    (hB : m64IntrinsicCurveVariation G σ 0 1 ≤ ENNReal.ofReal B) :
    ∃ (γ : ℝ → AnnulusCoordinates) (L : ℝ), 0 ≤ L ∧ L ≤ max B 0 ∧
      m64IntrinsicCurveVariation G γ 0 1 = ENNReal.ofReal L ∧
      ContinuousOn γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧ MapsTo γ (Icc 0 1) K ∧
      (∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
        G.edist (γ s) (γ t) ≤ ENNReal.ofReal (L * |s - t|)) ∧
      (∀ τ : ℝ → AnnulusCoordinates, ContinuousOn τ (Icc 0 1) →
        τ 0 = p → τ 1 = q → MapsTo τ (Icc 0 1) K →
        m64IntrinsicCurveVariation G γ 0 1 ≤ m64IntrinsicCurveVariation G τ 0 1) := by
  let : MetricSpace AnnulusCoordinates := intrinsicDistanceMetric G
  let : PseudoEMetricSpace AnnulusCoordinates :=
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace
  have hv : BoundedVariationOn σ (Icc 0 1) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  obtain ⟨γ, hγ0, hγ1, hγconf, hγlip, hγv, hγmin⟩ :=
    m64Intrinsic_exists_compact_constrained_minimizer hK hc h0 h1 hconf hv
  let L := (eVariationOn γ (Icc 0 1)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hlength : eVariationOn γ (Icc 0 1) = ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal hγv).symm
  have hLB : L ≤ max B 0 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((hγmin σ hc h0 h1 hconf).trans hB)
    simpa only [ENNReal.toReal_ofReal', L] using h
  refine ⟨γ, L, hL, hLB, hlength, hγlip.continuousOn, hγ0, hγ1, hγconf, ?_, ?_⟩
  · intro s hs t ht
    have h := hγlip hs ht
    change G.edist (γ s) (γ t) ≤
      (↑(eVariationOn γ (Icc 0 1)).toNNReal : ℝ≥0∞) * edist s t at h
    rw [ENNReal.coe_toNNReal hγv, hlength, edist_dist, Real.dist_eq,
      ← ENNReal.ofReal_mul hL] at h
    exact h
  · exact hγmin

theorem m64Intrinsic_exists_embedded_region_minimizer
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {p q : AnnulusCoordinates} {σ : ℝ → AnnulusCoordinates}
    (hc : ContinuousOn σ (Icc 0 1)) (h0 : σ 0 = p) (h1 : σ 1 = q)
    (hconf : MapsTo σ (Icc 0 1) K) {B : ℝ}
    (hB : m64IntrinsicCurveVariation G σ 0 1 ≤ ENNReal.ofReal B) :
    ∃ (γ : ℝ → AnnulusCoordinates) (L : ℝ), 0 ≤ L ∧ L ≤ max B 0 ∧
      ContinuousOn γ (Icc 0 L) ∧ γ 0 = p ∧ γ L = q ∧ MapsTo γ (Icc 0 L) K ∧
      InjOn γ (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        G.edist (γ s) (γ t) ≤ ENNReal.ofReal |s - t|) ∧
      (∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
        m64IntrinsicCurveVariation G γ a b = ENNReal.ofReal (b - a)) ∧
      (∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
        ∀ τ : ℝ → AnnulusCoordinates, ContinuousOn τ (Icc 0 1) →
          τ 0 = γ a → τ 1 = γ b → MapsTo τ (Icc 0 1) K →
          ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G τ 0 1) := by
  let : MetricSpace AnnulusCoordinates := intrinsicDistanceMetric G
  let : PseudoEMetricSpace AnnulusCoordinates :=
    (intrinsicDistanceMetric G).toEMetricSpace.toPseudoEMetricSpace
  have hv : BoundedVariationOn σ (Icc 0 1) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hB
  obtain ⟨γ, L, hL, hγ0, hγL, hγconf, hγunit, hγlip, hγinj, hγmin⟩ :=
    m64Intrinsic_exists_embedded_constrained_minimizer hK hc h0 h1 hconf hv
  have hLB : L ≤ max B 0 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((hγmin σ hc h0 h1 hconf).trans hB)
    simpa only [ENNReal.toReal_ofReal hL, ENNReal.toReal_ofReal'] using h
  refine ⟨γ, L, hL, hLB, hγlip.continuousOn, hγ0, hγL, hγconf, hγinj, ?_, ?_, ?_⟩
  · intro s hs t ht
    have h := hγlip hs ht
    change G.edist (γ s) (γ t) ≤ (↑(1 : ℝ≥0) : ℝ≥0∞) * edist s t at h
    simpa only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq] using h
  · intro a ha b hb
    have h := hγunit ha hb
    have hi : Icc 0 L ∩ Icc a b = Icc a b :=
      inter_eq_right.mpr (Icc_subset_Icc ha.1 hb.2)
    change eVariationOn γ (Icc a b) = ENNReal.ofReal (b - a)
    simpa only [hi, NNReal.coe_one, one_mul] using h
  · intro a ha b hb hab τ hτc hτa hτb hτconf
    apply m64Intrinsic_constrained_minimizer_subarc_unitInterval hL
      hγlip.continuousOn hγunit hγconf _ ha hb hab hτc hτa hτb hτconf
    simpa only [hγ0, hγL] using hγmin

end PoincareConjecture
