
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.LocalContinuity
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.ScaledContact
import PoincareConjecture.Proofs.M05.Analysis.Parabolic.LocalPreservation
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Persistence












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

omit [T2Space M] [CompactSpace M] [IsManifold (𝓡 3) ∞ M] in
private theorem finrank_tangent (x : M) :
    Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
  simp



theorem scaled_transportedRicciComplementTensor_mem
    (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (htrace : ∀ x : M, -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x)
    (hlog : ∀ x : M, 0 < (F.connection a).negativeCurvaturePart x →
      2 * (F.connection a).negativeCurvaturePart x *
        (Real.log ((F.connection a).negativeCurvaturePart x) + Real.log (1 + a) - 3) ≤
          (F.connection a).scalarCurvature x)
    {t : ℝ} (ht : t ∈ Ico a b) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    (1 + t) • transportedRicciComplementTensor F hC t x ∈ tensorRegion hn 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  obtain ⟨O, hO, hpO, e, heK, hU⟩ :=
    exists_scaled_transportedRicciComplementTensor_local_coordinates (M := M) F hC
      (finrank_tangent (M := M)) ht.2
  have cmp := @Poincare.Parabolic.local_mem_of_inward_of_contact M _ _ _
    (fun y : M => TensorFiber (TangentSpace (𝓡 3) y) 2)
    (fun y => inferInstance) (fun y => inferInstance) (fun y => inferInstance)
    (fun y => tensorRegion (finrank_tangent y) 0)
  have cmp' := @cmp
    (fun y => tensorRegion_nonempty (E := TangentSpace (𝓡 3) y)
      (finrank_tangent y) (show (0 : ℝ) ≤ 0 by rfl))
    (fun y => isClosed_tensorRegion (E := TangentSpace (𝓡 3) y)
      (finrank_tangent y) (show (0 : ℝ) ≤ 0 by rfl))
    (fun y => convex_tensorRegion (E := TangentSpace (𝓡 3) y)
      (finrank_tangent y) (show (0 : ℝ) ≤ 0 by rfl)) O hO hpO e heK
  have cmp'' := @cmp'
    (fun y s => (1 + s) • transportedRicciComplementTensor F hC s y)
    (fun y s => (1 + s) • transportedRicciComplementLaplacian F hC s y)
    (fun y s => scaledTensorReaction (E := TangentSpace (𝓡 3) y) s)
    a t
  have cmpU := cmp'' hU
  apply cmpU ?_ ?_ ?_ ?_ ?_ x t ⟨ht.1, le_rfl⟩
  · intro y s hs
    exact (hasDerivAt_scaled_transportedRicciComplementTensor F hC ha
      ⟨hs.1, hs.2.trans_lt ht.2⟩ y).hasDerivWithinAt
  · intro R
    obtain ⟨C, hC⟩ := exists_uniform_lipschitzOnWith_scaledTensorReaction
      (B := M) (V := (TangentSpace (𝓡 3) : M → Type _))
      (finrank_tangent (M := M)) R
    exact ⟨C, fun y s hs => hC y s (ha.trans hs.1.le)⟩
  · intro y s hs q hq
    exact scaledTensorReaction_inner_nonpos (E := TangentSpace (𝓡 3) y)
      (finrank_tangent y) (ha.trans hs.1.le) hq
  · intro y s hs q hq _ hactive hmax
    exact scaled_transportedRicciComplementLaplacian_nonpos_at_contact F hC hab
      ⟨hs.1.le, hs.2.trans_lt ht.2⟩ finrank_tangent y q hq hactive
      (Filter.Eventually.of_forall hmax)
  · intro y
    exact scaled_transportedRicciComplementTensor_initial_mem F hC ha hab y
      (finrank_tangent y) (htrace y) (hlog y)



theorem hamiltonIvey_pinching_persists
    (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (htrace : ∀ x : M,
      -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x)
    (hlog : ∀ x : M,
      0 < (F.connection a).negativeCurvaturePart x →
        2 * (F.connection a).negativeCurvaturePart x *
          (Real.log ((F.connection a).negativeCurvaturePart x) +
            Real.log (1 + a) - 3) ≤ (F.connection a).scalarCurvature x) :
    (∀ t ∈ Ico a b, ∀ x : M,
      -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x) ∧
    (∀ t ∈ Ico a b, ∀ x : M,
      0 < (F.connection t).negativeCurvaturePart x →
        2 * (F.connection t).negativeCurvaturePart x *
          (Real.log ((F.connection t).negativeCurvaturePart x) +
            Real.log (1 + t) - 3) ≤ (F.connection t).scalarCurvature x) := by
  refine ⟨scalar_lower_bound_persists_of_M04 ha hab F hC htrace, ?_⟩
  intro t ht x
  exact logarithmic_pinching_of_scaled_transportedRicciComplementTensor_mem
    F hC ha hab x (finrank_tangent x) ht
    (scaled_transportedRicciComplementTensor_mem ha hab F hC htrace hlog ht x
      (finrank_tangent x))

end PoincareConjecture.RicciFlow.Frame
