import PoincareConjecture.Proofs.M09.PullbackFrame

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem pullbackCovariantDerivative_extension_independent {J : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) (γ : ℝ → M)
    (Y : (t : ℝ) → TangentSpace (𝓡 n) (γ t)) (I : Set ℝ)
    (E E' : ParametricAlongCurveExtensionOn I γ Y) (s : ℝ) (hs : s ∈ I)
    (hI : UniqueDiffWithinAt ℝ I s)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    pullbackCovariantDerivative F time γ Y I E s =
      pullbackCovariantDerivative F time γ Y I E' s := by
  let b := (stdOrthonormalBasis ℝ V).toBasis
  let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) (γ s)
  have hq : γ s ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (γ s)
  have hE (A : ParametricAlongCurveExtensionOn I γ Y) :
      MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
        (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' V z.2 (A.extension z.1 z.2)) (s, γ s) :=
    (A.smooth.contMDiffAt (A.open_domain.mem_nhds (A.graph_mem s hs))).mdifferentiableAt
      (by simp)
  have hv : curveVelocityWithin γ I s = curveVelocity γ s :=
    congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) (γ s) ↦ L 1)
      (mfderivWithin_eq_mfderiv hI.uniqueMDiffWithinAt hγ)
  unfold pullbackCovariantDerivative
  rw [hv, parametric_pullback_frame (F.connection (time s)) b (γ s) γ s
    E.extension hq (hE E) hγ,
    parametric_pullback_frame (F.connection (time s)) b (γ s) γ s
      E'.extension hq (hE E') hγ]
  apply Finset.sum_congr rfl
  intro i _
  have heq : ∀ t ∈ I,
      e.localFrameCoeff (𝓡 n) b i (γ t) (E.extension t (γ t)) =
        e.localFrameCoeff (𝓡 n) b i (γ t) (E'.extension t (γ t)) := by
    intro t ht
    rw [E.agrees t ht, E'.agrees t ht]
  have hd (A : ParametricAlongCurveExtensionOn I γ Y) : DifferentiableAt ℝ
      (fun t ↦ e.localFrameCoeff (𝓡 n) b i (γ t) (A.extension t (γ t))) s :=
    (hasDerivAt_parametric_curve
      (fun z : ℝ × M ↦ e.localFrameCoeff (𝓡 n) b i z.2 (A.extension z.1 z.2)) γ s
      (mdifferentiableAt_parametric_frameCoeff b (γ s) (γ s) s
        A.extension hq (hE A) i) hγ).differentiableAt
  have hder : deriv
      (fun t ↦ e.localFrameCoeff (𝓡 n) b i (γ t) (E.extension t (γ t))) s =
      deriv (fun t ↦ e.localFrameCoeff (𝓡 n) b i (γ t) (E'.extension t (γ t))) s :=
    hI.eq_deriv I
      ((hd E).hasDerivAt.hasDerivWithinAt.congr_of_mem (fun t ht ↦ (heq t ht).symm) hs)
      (hd E').hasDerivAt.hasDerivWithinAt
  exact congrArg₂ (· + ·) (congrArg (· •
    (F.connection (time s)).connection (e.localFrame b i) (γ s) (curveVelocity γ s))
      (heq s hs)) (congrArg (· • e.localFrame b i (γ s)) hder)

end PoincareConjecture.Proofs.M09
