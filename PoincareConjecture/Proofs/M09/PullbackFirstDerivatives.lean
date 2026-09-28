import PoincareConjecture.Proofs.M09.NormalizedActionDerivative
import PoincareConjecture.Proofs.M09.ExponentialActionDifferential
import PoincareConjecture.Proofs.M09.ParametricCurveDerivative

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_first_derivatives_of_pullback {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M}
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (B : M × ℝ → ℝ)
    (hB : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B (A.gamma Z b, b))
    (hpull : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ B (A.gamma z.1 z.2, z.2)) =ᶠ[𝓝 (Z, b)]
        (fun z ↦ A.action z.1 z.2 / (2 * Real.sqrt z.2)))
    (hsurj : Function.Surjective (A.sliceDifferential Z b)) :
    (∀ v : TangentSpace (𝓡 n) (A.gamma Z b),
      mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (A.gamma Z b) v =
        (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v) ∧
    reducedLengthGradientNormSq F T B b (A.gamma Z b) =
      (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (A.gamma Z) b) (curveVelocity (A.gamma Z) b) ∧
    deriv (fun t ↦ B (A.gamma Z b, t)) b =
      ((F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        (F.metric (T - b)).inner (A.gamma Z b)
          (curveVelocity (A.gamma Z) b) (curveVelocity (A.gamma Z) b)) / 2 -
        B (A.gamma Z b, b) / (2 * b) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  have hden : 2 * Real.sqrt b ≠ 0 := (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).ne'
  have hBs := (hB.comp (A.gamma Z b)
    (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  have hγ := (lExponentialFamily_initialSlice_contMDiffAt A Z b hb hmax).mdifferentiableAt (by simp)
  have hAs := ((lExponentialFamily_action_contDiffOn hM04 hτmax hwindow A).contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (Z, b) ∈ Set.univ ×ˢ Set.Ioo 0 τmax from ⟨Set.mem_univ _, hb, hmax⟩))).comp Z
        (contDiffAt_id.prodMk contDiffAt_const)
  have hN : HasFDerivAt (fun Y : E ↦ A.action Y b / (2 * Real.sqrt b))
      ((2 * Real.sqrt b)⁻¹ • fderiv ℝ (fun Y ↦ A.action Y b) Z) Z := by
    convert! ((hAs.differentiableAt (by simp)).hasFDerivAt.const_mul
      (2 * Real.sqrt b)⁻¹) using 1 <;>
      simp only [Function.comp_def, id_eq, div_eq_mul_inv, mul_comm] <;> rfl
  have hpullS : (fun Y : E ↦ B (A.gamma Y b, b)) =ᶠ[𝓝 Z]
      (fun Y ↦ A.action Y b / (2 * Real.sqrt b)) :=
    hpull.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hcomp := (hBs.hasMFDerivAt.comp Z hγ.hasMFDerivAt).hasFDerivAt
  have hmaps := (hcomp.congr_of_eventuallyEq hpullS.symm).unique hN
  have hspace (v : TangentSpace (𝓡 n) (A.gamma Z b)) :
      mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (A.gamma Z b) v =
        (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v := by
    obtain ⟨W, rfl⟩ := hsurj v
    have heval := congrArg (fun L : E →L[ℝ] ℝ ↦ L W) hmaps
    change mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (A.gamma Z b) (A.sliceDifferential Z b W) =
      (2 * Real.sqrt b)⁻¹ * fderiv ℝ (fun Y ↦ A.action Y b) Z W at heval
    rw [lExponentialFamily_action_initial_differential hM04 hL hτmax hwindow A Z b hb hmax W]
      at heval
    simpa only [← mul_assoc, inv_mul_cancel₀ hden, one_mul] using heval
  refine ⟨hspace, reducedLengthGradientNormSq_eq_of_differential F T b B _ _ hspace, ?_⟩
  have hswap := (hB.comp (b, A.gamma Z b)
    (contMDiffAt_snd.prodMk contMDiffAt_fst)).mdifferentiableAt (by simp)
  have hcurve := (lExponentialFamily_gammaSlice_contMDiffAt A Z b hb hmax).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_parametric_curve (fun z : ℝ × M ↦ B (z.2, z.1))
    (A.gamma Z) b hswap hcurve
  have hpullT : (fun t ↦ B (A.gamma Z t, t)) =ᶠ[𝓝 b]
      (fun t ↦ A.action Z t / (2 * Real.sqrt t)) :=
    hpull.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hactual := (lExponentialFamily_normalizedAction_hasDerivAt hM04 hwindow A Z b hb hmax).congr_of_eventuallyEq
    hpullT
  have hd := hchain.unique hactual
  have hcenter := hpull.self_of_nhds
  dsimp only at hcenter hd
  rw [hspace, ← hcenter] at hd
  linarith

end PoincareConjecture.Proofs.M09
