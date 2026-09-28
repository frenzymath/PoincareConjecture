import PoincareConjecture.Proofs.M09.ChartCurveExtension
import PoincareConjecture.Proofs.M09.PullbackExtension









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def chartFieldExtensionAlong (p : M) (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) (v : ℝ → V)
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hv : ContDiffOn ℝ ∞ v U)
    (hq : ∀ s ∈ K, γ s ∈ (chartAt V p).source)
    (heq : ∀ s ∈ K, chartVectorField p (v s) (γ s) = Y s) :
    ParametricAlongCurveExtensionOn K γ Y where
  extension := fun s ↦ chartVectorField p (v s)
  domain := U ×ˢ (chartAt V p).source
  open_domain := hU.prod (chartAt V p).open_source
  graph_mem := fun s hs ↦ ⟨hKU hs, hq s hs⟩
  smooth := chartVectorField_param_smooth p v U hv
  agrees := heq

set_option backward.isDefEq.respectTransparency false in
theorem chartFieldExtensionAlong_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (p : M) (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) (v : ℝ → V)
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hv : ContDiffOn ℝ ∞ v U)
    (hq : ∀ s ∈ K, γ s ∈ (chartAt V p).source)
    (heq : ∀ s ∈ K, chartVectorField p (v s) (γ s) = Y s)
    (s : ℝ) (w : V) (hdv : HasDerivAt v w s) :
    pullbackCovariantDerivative F time γ Y K
      (chartFieldExtensionAlong p γ Y v U K hU hKU hv hq heq) s =
      chartVectorField p w (γ s) +
        (F.connection (time s)).connection (chartVectorField p (v s)) (γ s)
          (curveVelocityWithin (n := n) γ K s) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (time s)).toRiemannianMetric⟩
  let L : V →L[ℝ] TangentSpace (𝓡 n) (γ s) :=
    (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).inverse
  have hd : HasDerivAt (fun r ↦ L (v r)) (L w) s := by
    simpa only [zero_apply, zero_add] using (hasDerivAt_const s L).clm_apply hdv
  exact congrArg (· + (F.connection (time s)).connection
    (chartVectorField p (v s)) (γ s) (curveVelocityWithin (n := n) γ K s)) hd.deriv

theorem pullbackCovariantDerivative_chart_field_local {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (p : M) (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) (I U : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I γ Y)
    (s : ℝ) (hs : s ∈ I) (hU : IsOpen U) (hsU : s ∈ U)
    (hI : UniqueDiffWithinAt ℝ I s)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (v : ℝ → V) (hv : ContDiffOn ℝ ∞ v U)
    (hq : ∀ r ∈ I ∩ U, γ r ∈ (chartAt V p).source)
    (heq : ∀ r ∈ I ∩ U, chartVectorField p (v r) (γ r) = Y r)
    (w : V) (hdv : HasDerivAt v w s) :
    pullbackCovariantDerivative F time γ Y I E s =
      chartVectorField p w (γ s) +
        (F.connection (time s)).connection (chartVectorField p (v s)) (γ s)
          (curveVelocityWithin (n := n) γ I s) := by
  let K := I ∩ U
  let E' : ParametricAlongCurveExtensionOn K γ Y := {
    extension := E.extension
    domain := E.domain
    open_domain := E.open_domain
    graph_mem := fun r hr ↦ E.graph_mem r hr.1
    smooth := E.smooth
    agrees := fun r hr ↦ E.agrees r hr.1
  }
  have hK : UniqueDiffWithinAt ℝ K s := hI.inter (hU.mem_nhds hsU)
  have hvel : curveVelocityWithin (n := n) γ I s = curveVelocityWithin (n := n) γ K s := by
    unfold curveVelocityWithin
    rw [mfderivWithin_eq_mfderiv hI.uniqueMDiffWithinAt hγ,
      mfderivWithin_eq_mfderiv hK.uniqueMDiffWithinAt hγ]
  have hrestrict : pullbackCovariantDerivative F time γ Y I E s =
      pullbackCovariantDerivative F time γ Y K E' s := by
    unfold pullbackCovariantDerivative
    rw [hvel]
  rw [hrestrict, pullbackCovariantDerivative_extension_independent F time γ Y K E'
    (chartFieldExtensionAlong p γ Y v U K hU Set.inter_subset_right hv hq heq)
      s ⟨hs, hsU⟩ hK hγ,
    chartFieldExtensionAlong_pullback F time p γ Y v U K hU Set.inter_subset_right
      hv hq heq s w hdv, ← hvel]

theorem pullbackCovariantDerivative_chart_field_zero {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (p : M) (γ : ℝ → M)
    (Y : ∀ s, TangentSpace (𝓡 n) (γ s)) (I U : Set ℝ)
    (E : ParametricAlongCurveExtensionOn I γ Y)
    (s : ℝ) (hs : s ∈ I) (hU : IsOpen U) (hsU : s ∈ U)
    (hI : UniqueDiffWithinAt ℝ I s)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (v : ℝ → V) (hv : ContDiffOn ℝ ∞ v U)
    (hq : ∀ r ∈ I ∩ U, γ r ∈ (chartAt V p).source)
    (heq : ∀ r ∈ I ∩ U, chartVectorField p (v r) (γ r) = Y r)
    (w : V) (hdv : HasDerivAt v w s) (hzero : v s = 0) :
    pullbackCovariantDerivative F time γ Y I E s = chartVectorField p w (γ s) := by
  rw [pullbackCovariantDerivative_chart_field_local F time p γ Y I U E s hs hU hsU
    hI hγ v hv hq heq w hdv, hzero]
  have hfield : chartVectorField (n := n) p 0 = 0 := by
    funext x
    exact (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) x).inverse.map_zero
  rw [hfield, (F.connection (time s)).connection.zero]
  exact add_zero _

end PoincareConjecture.Proofs.M09
