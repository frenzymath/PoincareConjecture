import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_PhysicalCoordinateFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_OpenCoordinateRicci
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoefficientTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

theorem open_extChartAt_symm_apply {n : ℕ} (U : Opens (E n)) (q x : U) :
    (extChartAt (𝓡 n) q).symm (x : E n) = x := by
  have hcharts : extChartAt (𝓡 n) q = extChartAt (𝓡 n) x := by
    unfold extChartAt
    rw [show chartAt (E n) q = chartAt (E n) x by simp [Opens.chartAt_eq]]
  rw [hcharts]
  have h := extChartAt_to_inv (I := 𝓡 n) x
  rw [congrFun (open_extChartAt_coe U x) x] at h
  exact h

theorem coordinateFlowToTarget_pullbackCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) (E n) M ∞)
    (G : RicciFlow n (⟨e.source, e.open_source⟩ : Opens (E n)) J)
    (t : ℝ) (B : E n → SpacetimeBounds.MetricCoefficient n)
    (hB : ∀ (x : (⟨e.source, e.open_source⟩ : Opens (E n)))
      (v w : TangentSpace (𝓡 n) x), (G.metric t).inner x v w = B x v w)
    (p : (⟨e.target, e.open_target⟩ : Opens M))
    {x : E n} (hx : x ∈ e.source) :
    ((coordinateFlowToTarget e G).metric t).pullbackCoefficients (targetChart e p) x = B x := by
  let U : Opens (E n) := ⟨e.source, e.open_source⟩
  let xU : U := ⟨x, hx⟩
  let d := sourceTargetDiffeomorph e
  have hxchart : x ∈ (extChartAt (𝓡 n) xU).target := by
    have h := mem_extChartAt_target (I := 𝓡 n) xU
    rw [congrFun (open_extChartAt_coe U xU) xU] at h
    exact h
  have heq : targetChart e p =ᶠ[𝓝 x] d ∘ (extChartAt (𝓡 n) xU).symm := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    have he := open_extChartAt_symm_apply U xU (⟨y, hy⟩ : U)
    change (extChartAt (𝓡 n) xU).symm y = (⟨y, hy⟩ : U) at he
    apply Subtype.ext
    change (targetChart e p y).1 = (d ((extChartAt (𝓡 n) xU).symm y)).1
    rw [he, targetChart_val e p hy]
    rfl
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) xU).contMDiffAt
    ((isOpen_extChartAt_target xU).mem_nhds hxchart)
  have hcoeff := pullbackCoefficients_eq_of_metric_germ (G.metric t)
    ((coordinateFlowToTarget e G).metric t)
    (d.contMDiff.mdifferentiable (by simp) _) (hi.mdifferentiableAt (by simp)) heq
    (coordinateFlowToTarget_metric e G t ((extChartAt (𝓡 n) xU).symm x))
  exact hcoeff.trans ((open_pullbackCoefficients_germ U (G.metric t) hB xU).self_of_nhds)

end PoincareConjecture.M44
