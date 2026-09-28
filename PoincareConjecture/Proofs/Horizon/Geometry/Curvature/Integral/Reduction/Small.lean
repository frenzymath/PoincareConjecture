import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Small
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion
import Mathlib.MeasureTheory.Integral.Bochner.Set









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.RiemannianMetric

section Diffeomorph

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N] [T3Space M] [T3Space N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
  (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
  (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
    gM.inner x v w = gN.inner (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))

include hinner


theorem measurePreserving_diffeomorph :
    MeasurePreserving e gM.volumeMeasure gN.volumeMeasure := by
  have hm : Measurable (e : M → N) := e.toHomeomorph.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs]
  have h := volumeMeasure_image_diffeomorph gM gN e hinner (e ⁻¹' s)
  have he : Function.Surjective (e : M → N) := e.surjective
  rw [Set.image_preimage_eq _ he] at h
  exact h.symm



theorem integral_ball_diffeomorph (p : M) (r : ℝ) (h : N → ℝ) :
    (∫ x in gM.ball p r, h (e x) ∂gM.volumeMeasure) =
      ∫ x in gN.ball (e p) r, h x ∂gN.volumeMeasure := by
  have hi := (measurePreserving_diffeomorph gM gN e hinner).setIntegral_image_emb
    e.toHomeomorph.measurableEmbedding h (gM.ball p r)
  rw [image_ball_diffeomorph gM gN e hinner] at hi
  exact hi.symm



theorem integral_scalarCurvature_ball_diffeomorph
    (D : LeviCivitaData gM) (D' : LeviCivitaData gN) (p : M) (r : ℝ) :
    (∫ x in gM.ball p r, D.scalarCurvature x ∂gM.volumeMeasure) =
      ∫ x in gN.ball (e p) r, D'.scalarCurvature x ∂gN.volumeMeasure := by
  have hs : ∀ x : M, D.scalarCurvature x = D'.scalarCurvature (e x) := by
    intro x
    exact D.scalarCurvature_eq_of_local_isometry D' isOpen_univ
      e.contMDiff.contMDiffOn (fun y _ v w => hinner y v w) (mem_univ x)
  simp_rw [hs]
  exact integral_ball_diffeomorph gM gN e hinner p r D'.scalarCurvature

omit [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N] in


theorem sectionalCurvature_diffeomorph
    (D : LeviCivitaData gM) (D' : LeviCivitaData gN)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.sectionalCurvature x v w = D'.sectionalCurvature (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) := by
  unfold LeviCivitaData.sectionalCurvature
  rw [D.curvatureTensor_eq_of_local_isometry D' isOpen_univ
    e.contMDiff.contMDiffOn (fun y _ v w => hinner y v w) (mem_univ x)]
  rw [hinner x v v, hinner x w w, hinner x v w]

end Diffeomorph

section Shrink

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local instance smallCarrier : Small.{0} M :=
  Poincare.Topology.SecondCountable.small M

local instance smallChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} M) :=
  Poincare.Manifold.shrinkChartedSpace _ M

local instance smallIsManifold : IsManifold (𝓡 n) ∞ (Shrink.{0} M) :=
  Poincare.Manifold.shrinkIsManifold (𝓡 n) M

local instance smallT3Space : T3Space (Shrink.{0} M) :=
  (Poincare.Topology.SecondCountable.homeomorphShrink M).t3Space


def shrink (g : RiemannianMetric n M) : RiemannianMetric n (Shrink.{0} M) :=
  g.pullbackOfLocalDiffeomorph (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm.isLocalDiffeomorph

@[simp] theorem shrink_inner (g : RiemannianMetric n M)
    (x : Shrink.{0} M) (v w : TangentSpace (𝓡 n) x) :
    g.shrink.inner x v w = g.inner ((equivShrink M).symm x)
      (mfderiv (𝓡 n) (𝓡 n) (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x v)
      (mfderiv (𝓡 n) (𝓡 n) (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x w) :=
  rfl


theorem shrink_preconnectedSpace [PreconnectedSpace M] :
    PreconnectedSpace (Shrink.{0} M) :=
  (Poincare.Topology.SecondCountable.homeomorphShrink M).surjective.denseRange.preconnectedSpace
    (Poincare.Topology.SecondCountable.homeomorphShrink M).continuous

@[simp] theorem shrink_edist (g : RiemannianMetric n M) (x y : Shrink.{0} M) :
    g.shrink.edist x y = g.edist ((equivShrink M).symm x) ((equivShrink M).symm y) :=
  edist_diffeomorph g.shrink g (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm
    (fun _ _ _ => rfl) x y

theorem shrink_image_ball (g : RiemannianMetric n M) (x : Shrink.{0} M) (r : ℝ) :
    (equivShrink M).symm '' g.shrink.ball x r =
      g.ball ((equivShrink M).symm x) r :=
  image_ball_diffeomorph g.shrink g (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm
    (fun _ _ _ => rfl) x r

@[simp] theorem shrink_metricComplete_iff (g : RiemannianMetric n M) :
    MetricComplete g.shrink ↔ MetricComplete g :=
  metricComplete_iff_diffeomorph g.shrink g
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm (fun _ _ _ => rfl)

@[simp] theorem shrink_scalarCurvature (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (x : Shrink.{0} M) :
    g.shrink.leviCivitaData.scalarCurvature x = D.scalarCurvature ((equivShrink M).symm x) := by
  exact g.shrink.leviCivitaData.scalarCurvature_eq_of_local_isometry D isOpen_univ
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem shrink_sectionalCurvature (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (x : Shrink.{0} M) (v w : TangentSpace (𝓡 n) x) :
    g.shrink.leviCivitaData.sectionalCurvature x v w =
      D.sectionalCurvature ((equivShrink M).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x v)
        (mfderiv (𝓡 n) (𝓡 n) (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm x w) :=
  sectionalCurvature_diffeomorph g.shrink g
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm (fun _ _ _ => rfl)
    g.shrink.leviCivitaData D x v w


theorem shrink_sectionalCurvature_lower_bound (g : RiemannianMetric n M)
    (D : LeviCivitaData g) {κ : ℝ}
    (hsec : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), κ ≤ D.sectionalCurvature x v w) :
    ∀ (x : Shrink.{0} M) (v w : TangentSpace (𝓡 n) x),
      κ ≤ g.shrink.leviCivitaData.sectionalCurvature x v w := by
  intro x v w
  rw [shrink_sectionalCurvature g D]
  exact hsec _ _ _

section Volume

variable [MeasurableSpace M] [BorelSpace M]

local instance smallMeasurableSpace : MeasurableSpace (Shrink.{0} M) :=
  borel (Shrink.{0} M)

local instance smallBorelSpace : BorelSpace (Shrink.{0} M) := ⟨rfl⟩



theorem shrink_integral_scalarCurvature_ball (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (x : Shrink.{0} M) (r : ℝ) :
    (∫ y in g.shrink.ball x r, g.shrink.leviCivitaData.scalarCurvature y
      ∂g.shrink.volumeMeasure) =
      ∫ y in g.ball ((equivShrink M).symm x) r, D.scalarCurvature y ∂g.volumeMeasure :=
  integral_scalarCurvature_ball_diffeomorph g.shrink g
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm (fun _ _ _ => rfl)
    g.shrink.leviCivitaData D x r

end Volume
end Shrink

end PoincareConjecture.RiemannianMetric
