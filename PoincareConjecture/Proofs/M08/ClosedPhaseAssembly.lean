import PoincareConjecture.Proofs.M08.EndpointExtensionGluing
import PoincareConjecture.Proofs.M08.ManifoldEndpointExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in
theorem exists_closedEuler_extension_of_phase_cover {J C U : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    (hCclosed : IsClosed C) (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (hCU : C ⊆ U)
    (γ α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hαγ : EqOn α γ C) (htime : ∀ r ∈ C, T - r ^ 2 ∈ J)
    (hcover : ∀ s ∈ C, ∃ (a b : ℝ) (x : M) (Pbar : ℝ → EuclideanSpace ℝ (Fin n)),
      a < b ∧ s ∈ Icc a b ∧ Icc a b ⊆ C ∧ Icc a b ∈ 𝓝[C] s ∧
      MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      ∀ r ∈ Icc a b, HasDerivWithinAt
        (fun t ↦ (extChartAt (𝓡 n) x (γ t), Pbar t))
        (closedChartEulerPhase F T x (Icc a b) r (extChartAt (𝓡 n) x (γ r), Pbar r))
        (Icc a b) r) :
    ∃ E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C),
      ∀ s ∈ C, regularizedLGeodesicEquation F T α C E s := by
  apply exists_closedEuler_extension_of_local F T hCclosed hC hU hCU α hα
  intro s hs
  obtain ⟨a, b, x, Pbar, hab, hsab, habC, hnear, hsrcγ, hphase⟩ := hcover s hs
  let V := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hV : IsOpen V := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hVU : V ⊆ U := inter_subset_left
  have habV : Icc a b ⊆ V := by
    intro r hr
    refine ⟨hCU (habC hr), ?_⟩
    change α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source
    rw [hαγ (habC hr)]
    exact hsrcγ hr
  have hαV := hα.mono hVU
  have hsrcα : MapsTo α V (chartAt (EuclideanSpace ℝ (Fin n)) x).source :=
    fun r hr ↦ hr.2
  let e := extChartAt (𝓡 n) x
  have htarget : MapsTo (e ∘ γ) (Icc a b) e.target := by
    intro r hr
    apply e.map_source
    simpa only [e, extChartAt_source] using hsrcγ hr
  have hmomentum := closed_phase_momentum_of_eqOn F T x hV habV (uniqueDiffOn_Icc hab)
    (e ∘ γ) (e ∘ α) Pbar (chart_curve_contDiffOn x α hαV hsrcα)
    (fun r hr ↦ congrArg e (hαγ (habC hr))) htarget hphase
  let E := chartVelocityExtension hV x α hαV hsrcα
  have heq (r : ℝ) (hr : r ∈ Icc a b) : regularizedLGeodesicEquation F T α V E r := by
    intro W
    have h := closed_chart_momentum_regularized_equation F hM04 T hV habV
      (uniqueDiffOn_Icc hab) x α hαV hsrcα (fun t ht ↦ htime t (habC ht)) hr
        (hmomentum r hr) W
    unfold regularizedEulerResidual pullbackCovariantDerivative chartVelocityExtensionWithin at h
    rw [curveVelocityWithin_eq_of_uniqueDiff hV habV (uniqueDiffOn_Icc hab) α hαV hr] at h
    exact h
  obtain ⟨N, hN, hsN, hNC⟩ := mem_nhdsWithin.mp hnear
  let W := V ∩ N
  have hW : IsOpen W := hV.inter hN
  have hWV : W ⊆ V := inter_subset_left
  refine ⟨W, hW, ⟨habV hsab, hsN⟩, hWV.trans hVU,
    restrictParametricVelocityExtension hV hWV hW.uniqueDiffOn α hαV E, ?_⟩
  intro r hr hrC
  exact restrictParametricVelocityExtension_equation F T hV hWV hW.uniqueDiffOn α hαV E hr
    (heq r (hNC ⟨hr.2, hrC⟩))

theorem nonempty_regularizedData_of_closed_phase_cover {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (p : BackwardTimePath F T τ₁ τ₂)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (squareReparameterizedCurve p.curve)
      (sqrtParameterInterval τ₁ τ₂))
    (hcover : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      ∃ (a b : ℝ) (x : M) (Pbar : ℝ → EuclideanSpace ℝ (Fin n)),
        a < b ∧ s ∈ Icc a b ∧ Icc a b ⊆ sqrtParameterInterval τ₁ τ₂ ∧
        Icc a b ∈ 𝓝[sqrtParameterInterval τ₁ τ₂] s ∧
        MapsTo (squareReparameterizedCurve p.curve) (Icc a b)
          (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
        ∀ r ∈ Icc a b, HasDerivWithinAt
          (fun t ↦ (extChartAt (𝓡 n) x (p.curve (t ^ 2)), Pbar t))
          (closedChartEulerPhase F T x (Icc a b) r
            (extChartAt (𝓡 n) x (p.curve (r ^ 2)), Pbar r)) (Icc a b) r) :
    Nonempty (RegularizedLGeodesicData p) := by
  have hab : Real.sqrt τ₁ < Real.sqrt τ₂ :=
    Real.sqrt_lt_sqrt p.nonnegative p.ordered
  obtain ⟨α, U, hU, hCU, hα, hαγ⟩ := exists_smooth_manifold_extension_Icc hab
    (squareReparameterizedCurve p.curve) hsmooth
  have htime (r : ℝ) (hr : r ∈ sqrtParameterInterval τ₁ τ₂) : T - r ^ 2 ∈ J := by
    apply p.time_mem
    have hr0 : 0 ≤ r := (Real.sqrt_nonneg τ₁).trans hr.1
    constructor
    · nlinarith [Real.sq_sqrt p.nonnegative, Real.sqrt_nonneg τ₁, hr.1]
    · nlinarith [Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Real.sqrt_nonneg τ₂, hr.2]
  obtain ⟨E, hE⟩ := exists_closedEuler_extension_of_phase_cover F hM04 T isClosed_Icc
    (uniqueDiffOn_Icc hab) hU hCU (squareReparameterizedCurve p.curve) α hα hαγ htime hcover
  exact ⟨⟨⟨α, U, hU, hCU, hα, hαγ⟩, E, hE⟩⟩

end PoincareConjecture.M08
