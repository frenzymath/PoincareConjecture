import PoincareConjecture.Definitions.M62Curve
import PoincareConjecture.Proofs.M09.FrameForms
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Comp











set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.M62

open PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem hasDerivAt_metric_pairing {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {γ : ℝ → M}
    {Y Z : (s : ℝ) → TangentSpace (𝓡 n) (γ s)} {x : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ x)
    (hY : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s ↦ (⟨γ s, Y s⟩ : TangentBundle (𝓡 n) M)) x)
    (hZ : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s ↦ (⟨γ s, Z s⟩ : TangentBundle (𝓡 n) M)) x) :
    HasDerivAt (fun s ↦ g.inner (γ s) (Y s) (Z s))
      (g.inner (γ x) (rampHorizontalCovariantDerivative D γ Y x) (Z x) +
        g.inner (γ x) (Y x) (rampHorizontalCovariantDerivative D γ Z x)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let p := γ x
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let y : ℝ → EuclideanSpace ℝ (Fin n) := fun s ↦ (e ⟨γ s, Y s⟩).2
  let z : ℝ → EuclideanSpace ℝ (Fin n) := fun s ↦ (e ⟨γ s, Z s⟩).2
  let v : ℝ → TangentSpace (𝓡 n) p := fun s ↦ e.symmL ℝ p (y s)
  let w : ℝ → TangentSpace (𝓡 n) p := fun s ↦ e.symmL ℝ p (z s)
  have hy : DifferentiableAt ℝ y x := by
    rw [mdifferentiableAt_totalSpace] at hY
    exact hY.2.differentiableAt
  have hz : DifferentiableAt ℝ z x := by
    rw [mdifferentiableAt_totalSpace] at hZ
    exact hZ.2.differentiableAt
  have hv : HasDerivAt v (e.symmL ℝ p (deriv y x)) x :=
    (e.symmL ℝ p).hasFDerivAt.comp_hasDerivAt x hy.hasDerivAt
  have hw : HasDerivAt w (e.symmL ℝ p (deriv z x)) x :=
    (e.symmL ℝ p).hasFDerivAt.comp_hasDerivAt x hz.hasDerivAt
  have hvx : v x = Y x := by
    change e.symmL ℝ p (e ⟨p, Y x⟩).2 = Y x
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
    exact e.symmL_continuousLinearMapAt hp _
  have hwx : w x = Z x := by
    change e.symmL ℝ p (e ⟨p, Z x⟩).2 = Z x
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
    exact e.symmL_continuousLinearMapAt hp _
  let G := frameMetricForm g p
  have hG : MDifferentiableAt (𝓡 n)
      (𝓘(ℝ, TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ)) G p :=
    ((frameMetricForm_smooth g p).contMDiffAt (e.open_baseSet.mem_nhds hp)).mdifferentiableAt
      (by simp)
  have hGcurve : HasDerivAt (fun s ↦ G (γ s))
      (mvfderiv (𝓡 n) G p (curveVelocity γ x)) x := by
    exact (hG.hasMFDerivAt.comp x hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hpair := (hGcurve.clm_apply hv).clm_apply hw
  have heval (a b : TangentSpace (𝓡 n) p) :
      mvfderiv (𝓡 n) G p (curveVelocity γ x) a b =
        g.inner p (frozenConnectionEndomorphism D p (curveVelocity γ x) a) b +
          g.inner p a (frozenConnectionEndomorphism D p (curveVelocity γ x) b) := by
    let L := (ContinuousLinearMap.apply ℝ ℝ b).comp
      (ContinuousLinearMap.apply ℝ (TangentSpace (𝓡 n) p →L[ℝ] ℝ) a)
    have h := L.hasMFDerivAt.comp p hG.hasMFDerivAt
    have hvalue : mvfderiv (𝓡 n) (fun q ↦ G q a b) p (curveVelocity γ x) =
        mvfderiv (𝓡 n) G p (curveVelocity γ x) a b := by
      exact congrArg (fun A : TangentSpace (𝓡 n) p →L[ℝ] ℝ ↦ A (curveVelocity γ x))
        h.mfderiv
    rw [← hvalue]
    exact frameMetricForm_derivative D p (curveVelocity γ x) a b
  have hnear : ∀ᶠ s in 𝓝 x, γ s ∈ e.baseSet :=
    hγ.continuousAt (e.open_baseSet.mem_nhds hp)
  have hrep (s : ℝ) (hs : γ s ∈ e.baseSet)
      (A : (r : ℝ) → TangentSpace (𝓡 n) (γ r)) :
      extensionMap p (γ s) (e.symmL ℝ p (e ⟨γ s, A s⟩).2) = A s := by
    change e.symmL ℝ (γ s)
      (e.continuousLinearMapAt ℝ p (e.symmL ℝ p (e ⟨γ s, A s⟩).2)) = A s
    rw [e.continuousLinearMapAt_symmL hp,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hs]
    exact e.symmL_continuousLinearMapAt hs _
  have heq : (fun s ↦ g.inner (γ s) (Y s) (Z s)) =ᶠ[𝓝 x]
      (fun s ↦ G (γ s) (v s) (w s)) := by
    filter_upwards [hnear] with s hs
    dsimp only [G, frameMetricForm_apply, v, w, y, z]
    rw [hrep s hs Y, hrep s hs Z]
  apply (hpair.congr_of_eventuallyEq heq).congr_deriv
  simp only [hvx, hwx, add_apply, heval, G, p,
    frameMetricForm_self, rampHorizontalCovariantDerivative,
    frozenConnectionEndomorphism_apply, map_add]
  ring

end PoincareConjecture.M62
