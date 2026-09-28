import PoincareConjecture.Proofs.M08.ContinuationRegularized
import PoincareConjecture.Proofs.M08.RegularizedGeodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in

theorem backward_geodesic_eqOn_of_terminal_agreement [ConnectedSpace M] [T3Space M]
    {J : Set ℝ} {F : RicciFlow n M J} {T τmax τ₁ τ₂ : ℝ}
    (hM04 : RicciFlowCurvatureTheory.{u}) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 < τ₁) (hordered : τ₁ < τ₂) (hmax : τ₂ ≤ τmax)
    (q q' : BackwardTimePath F T 0 τ₂)
    (hq : IsBackwardLGeodesic F T 0 τ₂ q)
    (hq' : IsBackwardLGeodesic F T 0 τ₂ q')
    (htail : EqOn q.curve q'.curve (Icc τ₁ τ₂)) :
    EqOn q.curve q'.curve (Icc 0 τ₂) := by
  obtain ⟨R⟩ := nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hmax q hq
  obtain ⟨R'⟩ := nonempty_regularizedLGeodesicData hM04 hwindow hcurvature hmax q' hq'
  let α := squareReparameterizedCurve q.curve
  let β := squareReparameterizedCurve q'.curve
  have hα : IsContinuationCurve F T α (Ioo 0 (Real.sqrt τ₂)) := by
    simpa only [Real.sqrt_zero] using regularizedSquare_isContinuationCurve hM04 hwindow hmax q R
  have hβ : IsContinuationCurve F T β (Ioo 0 (Real.sqrt τ₂)) := by
    simpa only [Real.sqrt_zero] using regularizedSquare_isContinuationCurve hM04 hwindow hmax q' R'
  obtain ⟨s, hleft, hright⟩ := exists_between (Real.sqrt_lt_sqrt hτ₁.le hordered)
  have hs : s ∈ Ioo 0 (Real.sqrt τ₂) :=
    ⟨(Real.sqrt_nonneg τ₁).trans_lt hleft, hright⟩
  have hseed : α =ᶠ[𝓝 s] β := by
    filter_upwards [Ioo_mem_nhds hleft hright] with r hr
    exact htail (Ioo_subset_Icc_self (sq_mem_backward_interior hτ₁.le hr).2)
  have htime (r : ℝ) (hr : r ∈ Ioo 0 (Real.sqrt τ₂)) : T - r ^ 2 ∈ J := by
    apply interior_subset
    exact backwardSquareTime_mem_interior hwindow q.nonnegative q.ordered hmax
      (by simpa only [Real.sqrt_zero] using hr)
  have hopen : EqOn α β (Ioo 0 (Real.sqrt τ₂)) :=
    continuationCurve_eqOn_of_germ F hM04 T isOpen_Ioo isPreconnected_Ioo htime hα hβ hs hseed
  have hαc : ContinuousOn α (Icc 0 (Real.sqrt τ₂)) := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using squarePath_continuousOn q
  have hβc : ContinuousOn β (Icc 0 (Real.sqrt τ₂)) := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using squarePath_continuousOn q'
  have hclosure : Icc 0 (Real.sqrt τ₂) ⊆ closure (Ioo 0 (Real.sqrt τ₂)) := by
    rw [closure_Ioo (Real.sqrt_pos.mpr q.ordered).ne]
  have hclosed := hopen.of_subset_closure hαc hβc Ioo_subset_Icc_self hclosure
  intro τ hτ
  have h := hclosed ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hτ.2⟩
  simpa only [α, β, squareReparameterizedCurve, Real.sq_sqrt hτ.1] using h

end PoincareConjecture.M08
