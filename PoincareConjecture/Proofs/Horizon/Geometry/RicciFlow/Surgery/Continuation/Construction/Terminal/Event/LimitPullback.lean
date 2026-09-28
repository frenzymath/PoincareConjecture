import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Poincare.Analysis.Calculus

variable {M X : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]

theorem singularTensorCoefficient_pullback_eq
    (g : RiemannianMetric 3 M) {i : X → M} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (q : X) (a b : Fin 3) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    singularTensorCoefficient (singularMetricPullback g i) q a b z =
      bilinearBasisEvaluation a b
        (g.pullbackCoefficients (i ∘ (extChartAt (𝓡 3) q).symm) z) := by
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hz)).mdifferentiableAt (by simp)
  change g.inner (i ((extChartAt (𝓡 3) q).symm z))
    (mfderiv (𝓡 3) (𝓡 3) i _
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ a)))
    (mfderiv (𝓡 3) (𝓡 3) i _
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ b))) =
      g.inner (i ((extChartAt (𝓡 3) q).symm z))
        (mfderiv (𝓡 3) (𝓡 3) (i ∘ (extChartAt (𝓡 3) q).symm) z
          (EuclideanSpace.basisFun (Fin 3) ℝ a))
        (mfderiv (𝓡 3) (𝓡 3) (i ∘ (extChartAt (𝓡 3) q).symm) z
          (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [mfderiv_comp z (hi.mdifferentiable (by simp) _) hc]
  rfl

theorem CompactSingularMetricLimit.pullbackCoefficients_tendstoUniformlyOn
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {R : SingularTimeReference G T M} {gT : RiemannianMetric 3 X} {i : X → M}
    (h : CompactSingularMetricLimit R gT i) (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (q : X) (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3)))
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k
        ((R.flow.metric t).pullbackCoefficients (i ∘ (extChartAt (𝓡 3) q).symm)))
      (iteratedFDeriv ℝ k (gT.pullbackCoefficients (extChartAt (𝓡 3) q).symm))
      (𝓝[<] T) K := by
  have hchart (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ K) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds (hKt hx))
  apply tendstoUniformlyOn_bilinear_jets_of_components
    (fun t x hx => (R.flow.metric t).contDiffAt_pullbackCoefficients
      ((hi _).comp x (hchart x hx)))
    (fun x hx => gT.contDiffAt_pullbackCoefficients (hchart x hx))
  intro a b
  have hconv := h.tendstoUniformlyOn q a b k K hK hKt
  apply hconv.congr
  refine Eventually.of_forall fun t x hx => ?_
  have heq :
      singularTensorCoefficient (singularMetricPullback (R.flow.metric t) i) q a b =ᶠ[𝓝 x]
        (fun z => bilinearBasisEvaluation a b
          ((R.flow.metric t).pullbackCoefficients (i ∘ (extChartAt (𝓡 3) q).symm) z)) := by
    filter_upwards [(isOpen_extChartAt_target q).mem_nhds (hKt hx)] with z hz
    exact singularTensorCoefficient_pullback_eq (R.flow.metric t) hi q a b hz
  exact (heq.iteratedFDeriv ℝ k).self_of_nhds

end PoincareConjecture
