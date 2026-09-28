import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Proofs.M09.SmoothSquareActionDifferential
import PoincareConjecture.Proofs.M09.FamilySquareVelocity
import PoincareConjecture.Proofs.M09.NormalizedActionDerivative
import PoincareConjecture.Proofs.M09.ParametricCurveDerivative








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
theorem comparison_family_first_derivatives
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : E × ℝ → M) (Ω : Set (E × ℝ)) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f Ω)
    (hsegment : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ((0 : E), s) ∈ Ω)
    (hbase : ∀ s, f (0, s) = A.squareFamily Z s)
    (hfixed : ∀ x, f (x, 0) = p)
    (B : M × ℝ → ℝ)
    (hB : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ B (A.gamma Z b, b))
    (hpull : (fun z : E × ℝ ↦ B (f (z.1, Real.sqrt z.2), z.2)) =ᶠ[𝓝 (0, b)]
      (fun z ↦ backwardLLength F T 0 z.2 (fun t ↦ f (z.1, Real.sqrt t)) /
        (2 * Real.sqrt z.2)))
    (hsurj : Function.Surjective (mfderiv (𝓘(ℝ, E)) (𝓡 n)
      (fun x ↦ f (x, Real.sqrt b)) 0)) :
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
  let c := Real.sqrt b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hcmax : c < Real.sqrt τmax := Real.sqrt_lt_sqrt hb.le hmax
  have hden : 2 * c ≠ 0 := (mul_pos zero_lt_two hc).ne'
  have hsq : A.squareFamily Z c = A.gamma Z b := by
    rw [A.square_agrees Z c ⟨hc.le, hcmax⟩, hc2]
  have hfc : f (0, c) = A.gamma Z b := (hbase c).trans hsq
  let k : E → M := fun x ↦ f (x, c)
  let S : E → ℝ := fun x ↦ backwardLLength F T 0 b (fun t ↦ f (x, Real.sqrt t))
  have hk : MDifferentiableAt (𝓘(ℝ, E)) (𝓡 n) k 0 :=
    ((hf.contMDiffAt (hΩ.mem_nhds (hsegment c ⟨hc.le, le_rfl⟩))).comp 0
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt).mdifferentiableAt (by simp)
  have hBs : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun q ↦ B (q, b)) (k 0) := by
    rw [show k 0 = A.gamma Z b from hfc]
    exact (hB.comp (A.gamma Z b) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      (by simp)
  have hS : ContDiffAt ℝ ∞ S 0 := by
    have h := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
      f Ω hΩ hf ((0 : E), b) ⟨hb, hmax⟩ (fun r hr ↦ hsegment _
        ⟨mul_nonneg hc.le hr.1, mul_le_of_le_one_right hc.le hr.2⟩)
    exact h.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hN : HasFDerivAt (fun x : E ↦ S x / (2 * c))
      ((2 * c)⁻¹ • fderiv ℝ S 0) 0 := by
    convert! ((hS.differentiableAt (by simp)).hasFDerivAt.const_mul (2 * c)⁻¹) using 1 <;>
      simp only [Function.comp_def, id_eq, div_eq_mul_inv, mul_comm] <;> rfl
  have hpullS : (fun x : E ↦ B (k x, b)) =ᶠ[𝓝 0] (fun x ↦ S x / (2 * c)) :=
    hpull.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hcomp := (hBs.hasMFDerivAt.comp 0 hk.hasMFDerivAt).hasFDerivAt
  have hmaps := (hcomp.congr_of_eventuallyEq hpullS.symm).unique hN
  have hfirst (v : E) : fderiv ℝ S 0 v =
      (2 * c) * (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (A.gamma Z) b) (mfderiv (𝓘(ℝ, E)) (𝓡 n) k 0 v) := by
    have h := fderiv_smoothSquareFamily_action hM04 hL hτmax hwindow A Z b hb hmax
      f Ω hΩ hf 0 v hsegment (fun s _ ↦ hbase s)
    have hv : (curveVelocity (n := n) (fun r : ℝ ↦ f (0 + r • v, c)) 0 :
        EuclideanSpace ℝ (Fin n)) = mfderiv (𝓘(ℝ, E)) (𝓡 n) k 0 v :=
      curveVelocity_comp_initial_line k 0 v hk
    have hzero : (curveVelocity (n := n) (fun r : ℝ ↦ f (0 + r • v, 0)) 0 :
        EuclideanSpace ℝ (Fin n)) = 0 := by
      have heq : (fun r : ℝ ↦ f (0 + r • v, 0)) = (fun _ ↦ p) :=
        funext (fun _ ↦ hfixed _)
      rw [heq]
      simp only [curveVelocity, mfderiv_const, zero_apply]
    have hsvel := lExponentialFamily_square_velocity_eq A Z c ⟨hc, hcmax⟩
    rw [hc2] at hsvel
    rw [hv, hzero, map_zero, sub_zero, hsq, hsvel, map_smul, smul_apply, smul_eq_mul] at h
    exact h
  have hspace (v : TangentSpace (𝓡 n) (A.gamma Z b)) :
      mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (A.gamma Z b) v =
        (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v := by
    obtain ⟨x, hx⟩ := hsurj v
    have heval := congrArg (fun L : E →L[ℝ] ℝ ↦ L x) hmaps
    change mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (k 0)
      (mfderiv (𝓘(ℝ, E)) (𝓡 n) k 0 x) = (2 * c)⁻¹ * fderiv ℝ S 0 x at heval
    have hx' : (mfderiv (𝓘(ℝ, E)) (𝓡 n) k 0 x : EuclideanSpace ℝ (Fin n)) = v := hx
    rw [hfirst x, hx'] at heval
    rw [show k 0 = A.gamma Z b from hfc] at heval
    simpa only [← mul_assoc, inv_mul_cancel₀ hden, one_mul] using heval
  refine ⟨hspace, reducedLengthGradientNormSq_eq_of_differential F T b B _ _ hspace, ?_⟩
  have hpullT0 : (fun t ↦ B (f (0, Real.sqrt t), t)) =ᶠ[𝓝 b]
      (fun t ↦ backwardLLength F T 0 t (fun r ↦ f (0, Real.sqrt r)) /
        (2 * Real.sqrt t)) :=
    hpull.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hpullT : (fun t ↦ B (A.gamma Z t, t)) =ᶠ[𝓝 b]
      (fun t ↦ A.action Z t / (2 * Real.sqrt t)) := by
    filter_upwards [hpullT0, isOpen_Ioo.mem_nhds
      (show b ∈ Set.Ioo 0 τmax from ⟨hb, hmax⟩)] with t ht htime
    have hft : f (0, Real.sqrt t) = A.gamma Z t := by
      rw [hbase, A.square_agrees Z (Real.sqrt t)
        ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt htime.1.le htime.2⟩,
        Real.sq_sqrt htime.1.le]
    have hact : backwardLLength F T 0 t (fun r ↦ f (0, Real.sqrt r)) = A.action Z t := by
      apply backwardLLength_congr_Ioo F T 0 t htime.1.le
      intro r hr
      change f (0, Real.sqrt r) = A.gamma Z r
      rw [hbase, A.square_agrees Z (Real.sqrt r)
        ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt hr.1.le (hr.2.trans htime.2)⟩,
        Real.sq_sqrt hr.1.le]
    simpa only [hft, hact] using ht
  have hswap := (hB.comp (b, A.gamma Z b)
    (contMDiffAt_snd.prodMk contMDiffAt_fst)).mdifferentiableAt (by simp)
  have hcurve := (lExponentialFamily_gammaSlice_contMDiffAt A Z b hb hmax).mdifferentiableAt
    (by simp)
  have hchain := hasDerivAt_parametric_curve (fun z : ℝ × M ↦ B (z.2, z.1))
    (A.gamma Z) b hswap hcurve
  have hactual := (lExponentialFamily_normalizedAction_hasDerivAt hM04 hwindow A Z b hb hmax).congr_of_eventuallyEq hpullT
  have hd := hchain.unique hactual
  have hcenter := hpullT.self_of_nhds
  dsimp only at hd hcenter
  rw [hspace, ← hcenter] at hd
  linarith

end PoincareConjecture.Proofs.M09
