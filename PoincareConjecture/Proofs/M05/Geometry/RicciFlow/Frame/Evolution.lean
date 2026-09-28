import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.TransportInterval
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Curvature

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_curvature_transport (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Ico a b)) (hab : a < b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∃ U : ℝ → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      U a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Ico a b, HasDerivWithinAt U
        ((ricciEndomorphism F x t).comp (U t)) (Ico a b) t) ∧
      (∀ t ∈ Ico a b, ∀ v w,
        (F.metric t).inner x (U t v) (U t w) = (F.metric a).inner x v w) ∧
      (∀ t ∈ Ico a b, (U t).IsInvertible) ∧
      (∀ t ∈ Ioo a b, ∀ u v w z,
        HasDerivAt
          (fun s => (F.connection s).curvatureTensor x (U s u) (U s v) (U s w) (U s z))
          ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
              ![U t u, U t v, U t w, U t z] +
            2 * ((F.connection t).curvatureB x (U t u) (U t v) (U t w) (U t z) -
              (F.connection t).curvatureB x (U t u) (U t v) (U t z) (U t w) -
              (F.connection t).curvatureB x (U t u) (U t z) (U t v) (U t w) +
              (F.connection t).curvatureB x (U t u) (U t w) (U t v) (U t z))) t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  obtain ⟨U, hUa, hUd, hpair, hinv⟩ := exists_ricciTransport_on hC F hab x
  refine ⟨U, hUa, hUd, hpair, hinv, ?_⟩
  intro t ht u v w z
  have htab : t ∈ Ico a b := ⟨ht.1.le, ht.2⟩
  have hinput (q : TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => U s q)
        (ricciSharp (F.connection t) x (U t q)) (Ico a b) t := by
    have h := (hUd t htab).clm_apply (hasDerivWithinAt_const t (Ico a b) q)
    simpa only [map_zero, add_zero, ContinuousLinearMap.comp_apply,
      ricciEndomorphism_eq_sum F x htab, ricciSharp] using h
  have hinterior : t ∈ interior (Ico a b) := by
    simpa only [interior_Ico] using ht
  exact (hasDerivWithinAt_curvature_moving_inputs hC F hinterior x
    (fun s => U s u) (fun s => U s v) (fun s => U s w) (fun s => U s z)
    (hinput u) (hinput v) (hinput w) (hinput z)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hinterior)

end PoincareConjecture.RicciFlow.Frame
