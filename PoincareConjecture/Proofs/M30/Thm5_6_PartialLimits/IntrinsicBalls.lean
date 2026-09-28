import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement
import PoincareConjecture.Proofs.M13.Length
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.M30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
private theorem openInverse_contMDiffOn (U : TopologicalSpace.Opens M)
    (hne : Nonempty U) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (U.openPartialHomeomorphSubtypeCoe hne).symm (U : Set M) := by
  let e := U.openPartialHomeomorphSubtypeCoe hne
  intro y hy
  have heq : (Subtype.val ∘ e.symm) =ᶠ[𝓝 y] (id : M → M) := by
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    exact e.right_inv (by simpa only [e,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hz)
  apply ContMDiffAt.contMDiffWithinAt
  apply (ContMDiffAt.subtypeVal_comp_iff U e.symm y).mp
  exact contMDiffAt_id.congr_of_eventuallyEq heq

variable (g : RiemannianMetric n M) (U : TopologicalSpace.Opens M)
  (h : RiemannianMetric n U)
  (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
    h.inner x v w = g.inner (x : M)
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))

include hinner

private theorem subtype_pathELength {η : ℝ → U} {a b : ℝ}
    (hη : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 η (Icc a b)) :
    h.pathELength η a b = g.pathELength (Subtype.val ∘ η) a b := by
  rw [M13.pathELength_eq_lintegral_tangentNorm,
    M13.pathELength_eq_lintegral_tangentNorm]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  have hηt : MDifferentiableAt 𝓘(ℝ) (𝓡 n) η t :=
    ((hη.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  rw [mfderiv_comp t
    ((contMDiff_subtype_val (I := 𝓡 n) (U := U) (n := 1)).mdifferentiable
      one_ne_zero (η t)) hηt]
  change ENNReal.ofReal (Real.sqrt (h.inner (η t) _ _)) =
    ENNReal.ofReal (Real.sqrt (g.inner (η t : M) _ _))
  rw [hinner]
  rfl

private theorem exists_subtype_path {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) (U : Set M)) :
    ∃ η : ℝ → U, ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 η (Icc a b) ∧
      EqOn (Subtype.val ∘ η) γ (Icc a b) ∧
      h.pathELength η a b = g.pathELength γ a b := by
  let hne : Nonempty U := ⟨⟨γ a, hγU ⟨le_rfl, hab⟩⟩⟩
  let e := U.openPartialHomeomorphSubtypeCoe hne
  let η := e.symm ∘ γ
  have hη : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 η (Icc a b) :=
    ((openInverse_contMDiffOn U hne).of_le (by simp)).comp hγ hγU
  have heq : EqOn (Subtype.val ∘ η) γ (Icc a b) := by
    intro t ht
    exact e.right_inv (by simpa only [e,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hγU ht)
  refine ⟨η, hη, heq, ?_⟩
  rw [subtype_pathELength g U h hinner hη]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_congr heq

theorem intrinsic_edist_eq_of_ball_subset (p q : U) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (U : Set M))
    (hq : (q : M) ∈ g.ball (p : M) r) :
    h.edist p q = g.edist (p : M) (q : M) := by
  refine le_antisymm ?_
    (h.edist_map_le_of_metric_pullback g contMDiff_subtype_val hinner p q)
  apply le_of_forall_gt
  intro l hl
  obtain ⟨γ, h0, h1, hγ, hlen⟩ :=
    M13.exists_pathELength_lt g (lt_min hl hq)
  have hconf : MapsTo γ (Icc (0 : ℝ) 1) (g.ball (p : M) r) := by
    simpa only [h0] using
      g.mapsTo_ball_of_pathELength_lt hγ (hlen.trans_le (min_le_right _ _))
  obtain ⟨η, hη, heq, hlength⟩ :=
    exists_subtype_path g U h hinner zero_le_one hγ (fun _ ht => hball (hconf ht))
  have hη0 : η 0 = p := Subtype.ext ((heq (by norm_num)).trans h0)
  have hη1 : η 1 = q := Subtype.ext ((heq (by norm_num)).trans h1)
  calc
    h.edist p q ≤ h.pathELength η 0 1 := M13.edist_le_pathELength h hη hη0 hη1 zero_le_one
    _ = g.pathELength γ 0 1 := hlength
    _ < l := hlen.trans_le (min_le_left _ _)

theorem intrinsic_ball_eq_preimage (p : U) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (U : Set M)) :
    h.ball p r = (Subtype.val : U → M) ⁻¹' g.ball (p : M) r := by
  ext q
  change h.edist p q < ENNReal.ofReal r ↔ g.edist (p : M) (q : M) < ENNReal.ofReal r
  constructor
  · exact fun hq =>
      (h.edist_map_le_of_metric_pullback g contMDiff_subtype_val hinner p q).trans_lt hq
  · intro hq
    rwa [intrinsic_edist_eq_of_ball_subset g U h hinner p q hball hq]

theorem intrinsic_ball_image (p : U) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (U : Set M)) :
    (Subtype.val : U → M) '' h.ball p r = g.ball (p : M) r := by
  rw [intrinsic_ball_eq_preimage g U h hinner p hball]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hx
    exact ⟨⟨x, hball hx⟩, hx, rfl⟩

theorem intrinsic_closure_ball_eq_preimage (p : U) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (U : Set M)) :
    closure (h.ball p r) = (Subtype.val : U → M) ⁻¹' closure (g.ball (p : M) r) := by
  rw [intrinsic_ball_eq_preimage g U h hinner p hball]
  exact (U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val _).symm

theorem intrinsic_isCompact_closure_ball (p : U) {r : ℝ}
    (hcompact : IsCompact (closure (g.ball (p : M) r)))
    (hclosure : closure (g.ball (p : M) r) ⊆ (U : Set M)) :
    IsCompact (closure (h.ball p r)) := by
  rw [intrinsic_closure_ball_eq_preimage g U h hinner p (subset_closure.trans hclosure)]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
  intro x hx
  exact ⟨⟨x, hclosure hx⟩, rfl⟩

variable [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem intrinsic_calibratedMetricVolume_eq_image {B : Set U} (hB : MeasurableSet B) :
    calibratedMetricVolume h B = calibratedMetricVolume g ((Subtype.val : U → M) '' B) := by
  rw [calibratedMetricVolume_eq_volumeMeasure, calibratedMetricVolume_eq_volumeMeasure]
  exact (h.volumeMeasure_image_eq_of_injOn_metric_pullback g contMDiff_subtype_val hinner
    isOpen_univ (Set.injOn_of_injective Subtype.val_injective) hB (subset_univ B)).symm

theorem intrinsic_calibratedMetricVolume_ball (p : U) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (U : Set M)) :
    calibratedMetricVolume h (h.ball p r) = calibratedMetricVolume g (g.ball (p : M) r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 n) U
  have hB : MeasurableSet (h.ball p r) :=
    (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  rw [intrinsic_calibratedMetricVolume_eq_image g U h hinner hB,
    intrinsic_ball_image g U h hinner p hball]

end PoincareConjecture.M30
