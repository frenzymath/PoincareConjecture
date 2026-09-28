import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.CompactComparison

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem intrinsicEDist_le_of_tangentNorm_le
    (g h : RiemannianMetric 3 M) {U : Set M} {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v) (x y : M) :
    intrinsicEDist h U x y ≤ ENNReal.ofReal C * intrinsicEDist g U x y := by
  change intrinsicEDist h U x y ≤ ENNReal.ofReal C * sInf _
  rw [sInf_eq_iInf, ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top]
  apply le_iInf
  intro L
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top]
  apply le_iInf
  rintro ⟨γ, hγ, h0, h1, hU, rfl⟩
  have hl : intrinsicEDist h U x y ≤ h.pathELength γ 0 1 :=
    sInf_le ⟨γ, hγ, h0, h1, hU, rfl⟩
  exact hl.trans
    (g.pathELength_le_of_tangentNorm_le h γ 0 1 C hC.le
      (fun t ht => hbound (γ t) (hU ⟨t, ht, rfl⟩)))

theorem intrinsicDiameter_le_of_tangentNorm_le
    (g h : RiemannianMetric 3 M) {U : Set M} {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v) :
    intrinsicDiameter h U ≤ ENNReal.ofReal C * intrinsicDiameter g U := by
  apply sSup_le
  rintro _ ⟨p, rfl⟩
  exact (intrinsicEDist_le_of_tangentNorm_le g h hC hbound p.1 p.2).trans
    (mul_le_mul_right (show intrinsicEDist g U p.1 p.2 ≤ intrinsicDiameter g U from
      le_sSup ⟨p, rfl⟩) _)

theorem intrinsicDiameter_le_of_inner_le
    (g h : RiemannianMetric 3 M) {U : Set M} {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ C ^ 2 * g.inner x v v) :
    intrinsicDiameter h U ≤ ENNReal.ofReal C * intrinsicDiameter g U := by
  apply intrinsicDiameter_le_of_tangentNorm_le g h hC
  intro x hx v
  have hb := Real.sqrt_le_sqrt (hbound x hx v)
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le] at hb
  exact hb

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem eventually_terminal_intrinsicDiameter_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ t in 𝓝[<] T, ∀ U ⊆ A,
      intrinsicDiameter (H.terminalMetric P04) U ≤
        ENNReal.ofReal c * intrinsicDiameter ((H.terminalFlow P04).metric t) U ∧
      intrinsicDiameter ((H.terminalFlow P04).metric t) U ≤
        ENNReal.ofReal c * intrinsicDiameter (H.terminalMetric P04) U := by
  filter_upwards [H.eventually_terminal_tangentNorm_comparison P04 hA hc] with t ht U hU
  exact ⟨SingularRegularLimit.intrinsicDiameter_le_of_tangentNorm_le _ _ (zero_lt_one.trans hc)
      (fun x hx v => (ht x (hU hx) v).1),
    SingularRegularLimit.intrinsicDiameter_le_of_tangentNorm_le _ _ (zero_lt_one.trans hc)
      (fun x hx v => (ht x (hU hx) v).2)⟩

end PoincareConjecture.SingularTimeAssumptions
