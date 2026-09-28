import PoincareConjecture.Proofs.M09.ChartCurveExtension









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_chart_curve (p : M) (γ : ℝ → M) (s : ℝ)
    (hq : γ s ∈ (chartAt V p).source)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    HasDerivAt (fun t ↦ (chartAt V p) (γ t))
      (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s) (curveVelocity γ s)) s := by
  have he := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hq
  convert! (he.hasMFDerivAt.comp s hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt using 1

set_option backward.isDefEq.respectTransparency false in
theorem chartVectorField_coordinate_velocity (p : M) (γ : ℝ → M) (s : ℝ) (v : V)
    (hq : γ s ∈ (chartAt V p).source)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (ha : HasDerivAt (fun t ↦ (chartAt V p) (γ t)) v s) :
    chartVectorField p v (γ s) = curveVelocity γ s := by
  have hv := ha.unique (hasDerivAt_chart_curve p γ s hq hγ)
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hq, rfl⟩
  change (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).inverse v = _
  rw [hv]
  exact hi.inverse_apply_self _

noncomputable def chartVelocityExtensionAlong (p : M) (γ : ℝ → M) (v : ℝ → V)
    (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U) (hI : UniqueDiffOn ℝ I)
    (hv : ContDiffOn ℝ ∞ v U)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (ha : ∀ s ∈ I, HasDerivAt (fun t ↦ (chartAt V p) (γ t)) (v s) s)
    (hq : ∀ s ∈ I, γ s ∈ (chartAt V p).source) :
    ParametricAlongCurveExtensionOn I γ (curveVelocityWithin (n := n) γ I) where
  extension := fun s ↦ chartVectorField p (v s)
  domain := U ×ˢ (chartAt V p).source
  open_domain := hU.prod (chartAt V p).open_source
  graph_mem := fun s hs ↦ ⟨hIU hs, hq s hs⟩
  smooth := chartVectorField_param_smooth p v U hv
  agrees := by
    intro s hs
    rw [chartVectorField_coordinate_velocity p γ s (v s) (hq s hs) (hγ s hs) (ha s hs)]
    exact (congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) (γ s) ↦ L 1)
      (mfderivWithin_eq_mfderiv (hI s hs).uniqueMDiffWithinAt (hγ s hs))).symm

set_option backward.isDefEq.respectTransparency false in
theorem chartVelocityExtensionAlong_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (p : M) (γ : ℝ → M) (v : ℝ → V)
    (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U) (hI : UniqueDiffOn ℝ I)
    (hv : ContDiffOn ℝ ∞ v U)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (ha : ∀ s ∈ I, HasDerivAt (fun t ↦ (chartAt V p) (γ t)) (v s) s)
    (hq : ∀ s ∈ I, γ s ∈ (chartAt V p).source)
    (s : ℝ) (hs : s ∈ I) (w : V) (hdv : HasDerivAt v w s) :
    pullbackCovariantDerivative F time γ (curveVelocityWithin (n := n) γ I) I
      (chartVelocityExtensionAlong p γ v U I hU hIU hI hv hγ ha hq) s =
      chartVectorField p w (γ s) +
        (F.connection (time s)).connection (chartVectorField p (v s)) (γ s)
          (curveVelocityWithin (n := n) γ I s) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (time s)).toRiemannianMetric⟩
  let L : V →L[ℝ] TangentSpace (𝓡 n) (γ s) :=
    (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).inverse
  have hd : HasDerivAt (fun r ↦ L (v r)) (L w) s := by
    simpa only [zero_apply, zero_add] using (hasDerivAt_const s L).clm_apply hdv
  exact congrArg (· + (F.connection (time s)).connection
    (chartVectorField p (v s)) (γ s) (curveVelocityWithin (n := n) γ I s)) hd.deriv

end PoincareConjecture.Proofs.M09
