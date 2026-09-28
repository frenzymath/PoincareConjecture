import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def connectedComponentMetric (g : RiemannianMetric n M) (p : M) :
    RiemannianMetric n (Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :=
  g.pullbackOfLocalDiffeomorph Subtype.val
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) _)

omit [IsManifold (𝓡 n) ∞ M] in
private theorem contMDiff_subtype_mk {U : Opens M} {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) (hU : ∀ t, γ t ∈ U) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun t => (⟨γ t, hU t⟩ : U)) := by
  intro t
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp 𝓘(ℝ, ℝ) (𝓡 n) 1)
    (fun t => (⟨γ t, hU t⟩ : U)) univ t).mp (hγ t)

theorem pathELength_subtype_val {U : Opens M}
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (γ : ℝ → U) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) (a b : ℝ) :
    gU.pathELength γ a b = g.pathELength (Subtype.val ∘ γ) a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  unfold pathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro t
  rw [mfderiv_comp t ((contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero (γ t))
    (hγ.mdifferentiable one_ne_zero t)]
  simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
  apply NNReal.eq
  change ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1‖ =
    ‖mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)‖
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (hinner (γ t) _ _)

theorem edist_subtype_val {U : Opens M} (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (x y : U) : gU.edist x y = g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  apply le_antisymm
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    have hU : ∀ t, γ t ∈ U := by
      intro t
      apply (show IsClopen (U : Set M) from ⟨hclosed, U.isOpen⟩).connectedComponent_subset
        (show γ 0 ∈ U by simpa [h0] using x.property)
      apply hγ.continuous.mapsTo_connectedComponent 0
      simp
    let γU : ℝ → U := fun t => ⟨γ t, hU t⟩
    have hγU : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γU := contMDiff_subtype_mk hγ hU
    have hle : gU.edist x y ≤ gU.pathELength γU 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγU.contMDiffOn
        (Subtype.ext h0) (Subtype.ext h1) zero_le_one
    rw [pathELength_subtype_val g gU hinner γU hγU] at hle
    exact hle.trans_lt hlen
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    have hle : g.edist x y ≤ g.pathELength (Subtype.val ∘ γ) 0 1 :=
      Manifold.riemannianEDist_le_pathELength
        (contMDiff_subtype_val.comp hγ).contMDiffOn
        (congrArg Subtype.val h0) (congrArg Subtype.val h1) zero_le_one
    rw [← pathELength_subtype_val g gU hinner γ hγ] at hle
    exact hle.trans_lt hlen

theorem mem_of_edist_lt_top {U : Opens M} (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) {x y : M} (hx : x ∈ U)
    (hxy : g.edist x y < ⊤) : y ∈ U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
  apply (show IsClopen (U : Set M) from ⟨hclosed, U.isOpen⟩).connectedComponent_subset hx
  rw [← h0, ← h1]
  apply hγ.continuous.mapsTo_connectedComponent 0
  simp

theorem image_ball_subtype_val {U : Opens M} (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (x : U) (r : ℝ) :
    Subtype.val '' gU.ball x r = g.ball x r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [ball, mem_ofPred_eq, edist_subtype_val hclosed g gU hinner] using hz
  · intro hy
    have hyU : y ∈ U := mem_of_edist_lt_top hclosed g x.property
      ((show g.edist x y < ENNReal.ofReal r from hy).trans_le le_top)
    refine ⟨⟨y, hyU⟩, ?_, rfl⟩
    simpa only [ball, mem_ofPred_eq, edist_subtype_val hclosed g gU hinner] using hy

theorem metricComplete_of_subtype_val [T3Space M] {U : Opens M}
    (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (hcomplete : MetricComplete g) : MetricComplete gU := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let mM : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : CompleteSpace M := hcomplete
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let mU : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 n) U
  have hi : @Isometry U M mU.toPseudoEMetricSpace mM.toPseudoEMetricSpace Subtype.val :=
    fun x y => (edist_subtype_val hclosed g gU hinner x y).symm
  have hui := @Isometry.isUniformInducing U M mU.toPseudoEMetricSpace
    mM.toPseudoEMetricSpace Subtype.val hi
  apply @IsUniformInducing.completeSpace U M mU.toUniformSpace mM.toUniformSpace
    Subtype.val hui
  rw [Subtype.range_coe_subtype]
  change @IsComplete M mM.toUniformSpace (U : Set M)
  exact @IsClosed.isComplete M mM.toUniformSpace hcomplete (U : Set M) hclosed

theorem volumeMeasure_ball_subtype_val [T3Space M] [MeasurableSpace M] [BorelSpace M]
    {U : Opens M} (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (x : U) (r : ℝ) :
    gU.volumeMeasure (gU.ball x r) = g.volumeMeasure (g.ball x r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let mM : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let mU : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 n) U
  have hi : @Isometry U M mU.toPseudoEMetricSpace mM.toPseudoEMetricSpace Subtype.val :=
    fun x y => (edist_subtype_val hclosed g gU hinner x y).symm
  have h := @Isometry.euclideanHausdorffMeasure_image U M mU _ _ mM _ _
    Subtype.val n hi (gU.ball x r)
  change g.volumeMeasure (Subtype.val '' gU.ball x r) =
    gU.volumeMeasure (gU.ball x r) at h
  simpa only [image_ball_subtype_val hclosed g gU hinner] using h.symm

end PoincareConjecture.RiemannianMetric
