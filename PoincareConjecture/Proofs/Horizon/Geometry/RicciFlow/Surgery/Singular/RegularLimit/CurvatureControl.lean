import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.RegularSet
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem curvature_norm_le_of_scalar_le (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t B : ℝ} (ht : t ∈ F.interval)
    (x : (F.slice t).carrier) (hR : (F.connection t).scalarCurvature x ≤ B) :
    (F.connection t).curvatureTensorNorm x ≤ 13 * max B (Real.exp 4) := by
  obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
    (F.connection t).three_dimensional_curvature_spectrum
      (P04.tensor_calculus 3 (F.slice t).carrier (F.metric t) (F.connection t)) x
  have hpinch : 0 < max (-k3) 0 →
      2 * max (-k3) 0 * (Real.log (max (-k3) 0) + Real.log (1 + t) - 3) ≤
        2 * (k1 + k2 + k3) := by
    intro hX
    have h := H.hamilton_ivey_pinching ⟨t, x⟩ ht
    simpa [LeviCivitaData.negativeCurvaturePart, hleast, hscalar,
      GeneralizedRicciFlowData.scalar] using h (by
        simpa [LeviCivitaData.negativeCurvaturePart, hleast] using hX)
  rw [hscalar] at hR
  exact Poincare.fullNorm_le_of_hamiltonIvey (H.interval_nonnegative ht)
    h12 h23 rfl hnorm hR hpinch

theorem reference_curvature_norm_le_of_scalar_le (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t B : ℝ}
    (ht : t ∈ Ico H.reference.tMinus T) (x : M) (hR : H.reference.scalar t x ≤ B) :
    (H.reference.flow.connection t).curvatureTensorNorm x ≤ 13 * max B (Real.exp 4) := by
  rw [(H.reference.flow.connection t).curvatureTensorNorm_eq_of_local_isometry
    (F.connection t) isOpen_univ (H.reference.forward_smooth t ht).contMDiffOn
    (fun y _ v w => (H.reference.metric_pullback t ht y v w).symm) (mem_univ x)]
  apply H.curvature_norm_le_of_scalar_le P04 (H.reference.window_subset ht)
  simpa only [H.reference.scalar_pullback, SingularTimeReference.scalar] using hR

theorem exists_open_uniform_curvature_tail (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    ∃ (s K : ℝ) (U : Set M), H.reference.tMinus < s ∧ s < T ∧ 0 < K ∧
      IsOpen U ∧ x ∈ U ∧ U ⊆ H.reference.regularLimitSet ∧
        ∀ t ∈ Ico s T, ∀ y ∈ U,
          (H.reference.flow.connection t).curvatureTensorNorm y ≤ K := by
  obtain ⟨s, B, U, hs, hsT, _, hU, hxU, hsub, hbound⟩ :=
    H.exists_open_uniform_scalar_tail P04 hx
  refine ⟨s, 13 * max B (Real.exp 4), U, hs, hsT, ?_, hU, hxU, hsub, ?_⟩
  · positivity
  · intro t ht y hy
    exact H.reference_curvature_norm_le_of_scalar_le P04 ⟨hs.le.trans ht.1, ht.2⟩ y
      (hbound t ht y hy)

end PoincareConjecture.SingularTimeAssumptions
