import PoincareConjecture.Proofs.M47.LimitFiniteEndpointFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

variable {ι M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]
  (U : ι → TopologicalSpace.Opens M) (W : ι → Set E) (hW : ∀ i, IsOpen (W i))
  [∀ i, Nonempty (Piece W i)]

variable (Φ : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) E (U i) ∞)
  (hsource : ∀ i, W i ⊆ (Φ i).source)

include hsource in
omit [IsManifold (𝓡 3) ∞ M] in

theorem limitFinite_endpoint_chart_maps :
    letI : ∀ i, ChartedSpace E (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
    let q : ∀ i, Piece W i → M := fun i x => (Φ i x).val
    (∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i)) ∧
      (∀ i (x : Piece W i) (v : E), mfderiv (𝓡 3) (𝓡 3) (q i) x v =
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U i → M) (Φ i x)
          (mfderiv (𝓡 3) (𝓡 3) (Φ i) (x : E) v)) ∧
      ∀ i, range (q i) = (fun z : E => (Φ i z).val) '' W i := by
  let : ∀ i, ChartedSpace E (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let q : ∀ i, Piece W i → M := fun i x => (Φ i x).val
  have hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i) := by
    intro i x
    have hp := (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (W i) (hW i) ∞ x).comp
      (𝓡 3) (U i) ((Φ i).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (hsource i x.property))
    exact hp.comp (𝓡 3) M (Poincare.isLocalDiffeomorph_opensSubtypeVal
      (𝓡 3) (U i) (Φ i x))
  refine ⟨hq, ?_, ?_⟩
  · intro i x v
    have hnear : ChartDistance.chartParametrization W hW (q i) =ᶠ[𝓝 (x : E)]
        (fun z : E => (Φ i z).val) := by
      filter_upwards [(hW i).mem_nhds x.property] with z hz
      exact ChartDistance.chartParametrization_apply W hW (q i) ⟨z, hz⟩
    have hd := ChartDistance.mfderiv_chartParametrization W hW x ((hq i).contMDiff x)
    rw [hnear.mfderiv_eq] at hd
    have hc := mfderiv_comp (x : E)
      ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U i)).mdifferentiable
        (by simp) (Φ i x))
      ((Φ i).mdifferentiableAt (by simp) (hsource i x.property))
    exact (congrArg (fun L => L v) hd).symm.trans (congrArg (fun L => L v) hc)
  · intro i
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

include hsource in
omit [IsManifold (𝓡 3) ∞ M] in

theorem limitFinite_endpoint_chart_pairing
    (B : ι → E → Bilin)
    (hpair : ∀ i j (x : Piece W i) (y : Piece W j), (Φ i x).val = (Φ j y).val →
      ∀ a b c d : E,
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U i → M) (Φ i x)
            (mfderiv (𝓡 3) (𝓡 3) (Φ i) (x : E) a) =
          mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → M) (Φ j y)
            (mfderiv (𝓡 3) (𝓡 3) (Φ j) (y : E) c) →
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U i → M) (Φ i x)
            (mfderiv (𝓡 3) (𝓡 3) (Φ i) (x : E) b) =
          mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → M) (Φ j y)
            (mfderiv (𝓡 3) (𝓡 3) (Φ j) (y : E) d) →
        B i x a b = B j y c d) :
    letI : ∀ i, ChartedSpace E (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
    ∀ (g : ∀ i, RiemannianMetric 3 (Piece W i)),
      (∀ i (x : Piece W i) v w, (g i).inner x v w = B i x v w) →
    let q : ∀ i, Piece W i → M := fun i x => (Φ i x).val
    ∀ i j (x : Piece W i) (y : Piece W j), q i x = q j y → ∀ a b c d : E,
      mfderiv (𝓡 3) (𝓡 3) (q i) x a = mfderiv (𝓡 3) (𝓡 3) (q j) y c →
      mfderiv (𝓡 3) (𝓡 3) (q i) x b = mfderiv (𝓡 3) (𝓡 3) (q j) y d →
      (g i).inner x a b = (g j).inner y c d := by
  let : ∀ i, ChartedSpace E (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
  intro g hcoeff
  obtain ⟨_hq, hd, _himage⟩ := limitFinite_endpoint_chart_maps U W hW Φ hsource
  dsimp only
  intro i j x y hxy a b c d ha hb
  rw [hcoeff, hcoeff]
  apply hpair i j x y hxy a b c d
  · simpa only [hd] using ha
  · simpa only [hd] using hb

include hsource in

theorem limitFinite_endpoint_chart_old_metric
    (g0 : RiemannianMetric 3 M)
    (B : ι → E → Bilin)
    (hB : ∀ i (x : Piece W i), B i x =
      (g0.pullbackOfLocalDiffeomorph (Subtype.val : U i → M)
        (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U i))).pullbackCoefficients
          (Φ i) x) :
    letI : ∀ i, ChartedSpace E (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
    ∀ (g : ∀ i, RiemannianMetric 3 (Piece W i)),
      (∀ i (x : Piece W i) v w, (g i).inner x v w = B i x v w) →
    let q : ∀ i, Piece W i → M := fun i x => (Φ i x).val
    ∀ i (x : Piece W i) (v w : E), (g i).inner x v w = g0.inner (q i x)
      (mfderiv (𝓡 3) (𝓡 3) (q i) x v) (mfderiv (𝓡 3) (𝓡 3) (q i) x w) := by
  let : ∀ i, ChartedSpace E (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
  intro g hcoeff
  obtain ⟨_hq, hd, _himage⟩ := limitFinite_endpoint_chart_maps U W hW Φ hsource
  dsimp only
  intro i x v w
  rw [hcoeff, hB, hd, hd]
  rfl

end PoincareConjecture.M47
