import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationCurvature
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingConnection
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ}




theorem angular_velocity_periodic (gamma : C1FreeLoopSpace (M := M)) :
    Function.Periodic (fun x =>
      (curveVelocity (n := 3) (periodicFreeLoop gamma) x : LoopAmbient)) rampPeriod := by
  let c := periodicFreeLoop gamma
  have hp : Function.Periodic c rampPeriod := Proofs.M58.periodic_periodicFreeLoop gamma
  intro x
  have hh := m65CurveVelocity_comp (gamma := c) (phi := fun y => y + rampPeriod) (x := x)
    ((Proofs.M58.contMDiff_periodicFreeLoop gamma (x + rampPeriod)).mdifferentiableAt
      one_ne_zero) ((hasDerivAt_id x).add_const rampPeriod)
  have he : c ∘ (fun y => y + rampPeriod) = c := funext hp
  have hh0 : (curveVelocity (n := 3) c (x + rampPeriod) : LoopAmbient) =
      (curveVelocity (n := 3) (c ∘ (fun y => y + rampPeriod)) x : LoopAmbient) := by
    simpa only [one_smul] using hh.symm
  exact hh0.trans (congrArg (fun f : ℝ → M =>
    (curveVelocity (n := 3) f x : LoopAmbient)) he)




theorem time_velocity_periodic (loops : ℝ → C1FreeLoopSpace (M := M)) (t : ℝ) :
    Function.Periodic (fun x =>
      (curveVelocity (n := 3) (fun q => periodicFreeLoop (loops q) x) t : LoopAmbient))
        rampPeriod := by
  intro x
  exact congrArg (fun c : ℝ → M => (curveVelocity (n := 3) c t : LoopAmbient))
    (funext (fun q => Proofs.M58.periodic_periodicFreeLoop (loops q) x))




theorem curvature_periodic (F : RicciFlow 3 M (Icc a b))
    (loops : ℝ → C1FreeLoopSpace (M := M)) (t : ℝ) :
    Function.Periodic (fun x =>
      (m62CurvatureVector F (fun y q => periodicFreeLoop (loops q) y) t x : LoopAmbient))
        rampPeriod := by
  let c := periodicFreeLoop (loops t)
  have hp : Function.Periodic c rampPeriod := Proofs.M58.periodic_periodicFreeLoop (loops t)
  have hv : Function.Periodic (fun x => (curveVelocity (n := 3) c x : LoopAmbient))
      rampPeriod := angular_velocity_periodic (loops t)
  let speed := fun x => (F.metric t).tangentNorm (c x) (curveVelocity (n := 3) c x)
  have hs : Function.Periodic speed rampPeriod :=
    Proofs.M58.periodic_freeLoopSpeed (F.metric t) (loops t)
  let Y := fun x => (speed x)⁻¹ • curveVelocity (n := 3) c x
  have hY : Function.Periodic (fun x => (Y x : LoopAmbient)) rampPeriod := by
    intro x
    dsimp only [Y]
    simp +instances only [hs x, hv x]
  intro x
  let e := trivializationAt LoopAmbient (TangentSpace (𝓡 3) : M → Type _) (c x)
  let v := fun y => (e ⟨c y, Y y⟩).2
  have hvp : Function.Periodic v rampPeriod := by
    intro y
    dsimp only [v]
    simp +instances only [hY y]
    exact congrArg (fun p => (e ⟨p, (Y y : TangentSpace (𝓡 3) p)⟩).2) (hp y)
  have hd : deriv v (x + rampPeriod) = deriv v x := by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f : ℝ → LoopAmbient => deriv f x) (funext hvp)
  change (speed (x + rampPeriod))⁻¹ •
    rampHorizontalCovariantDerivative (F.connection t) c Y (x + rampPeriod) =
      (speed x)⁻¹ • rampHorizontalCovariantDerivative (F.connection t) c Y x
  rw [hs x]
  congr 1
  let B (p : M) (y w : LoopAmbient) (s : ℝ) : LoopAmbient :=
    let ep := trivializationAt LoopAmbient (TangentSpace (𝓡 3) : M → Type _) p
    ep.symmL ℝ p (deriv (fun z => (ep ⟨c z, Y z⟩).2) s) +
      (F.connection t).connection
        (FiberBundle.extend LoopAmbient (x := p) (y : TangentSpace (𝓡 3) p)) p
          (w : TangentSpace (𝓡 3) p)
  change B (c (x + rampPeriod)) (Y (x + rampPeriod)) (curveVelocity c (x + rampPeriod))
      (x + rampPeriod) = B (c x) (Y x) (curveVelocity c x) x
  exact (congrArg (fun p => B p (Y (x + rampPeriod))
    (curveVelocity c (x + rampPeriod)) (x + rampPeriod)) (hp x)).trans
    ((congrArg₂ (fun y w : LoopAmbient => B (c x) y w (x + rampPeriod))
      (hY x) (hv x)).trans
      (congrArg (fun w => (e.symmL ℝ (c x) w +
        (F.connection t).connection (FiberBundle.extend LoopAmbient (Y x))
          (c x) (curveVelocity c x) : LoopAmbient)) hd))




theorem residual_periodic (F : RicciFlow 3 M (Icc a b))
    (loops : ℝ → C1FreeLoopSpace (M := M)) (t : ℝ) :
    Function.Periodic (fun x => (F.metric t).tangentNorm (periodicFreeLoop (loops t) x)
      (curveVelocity (n := 3) (fun q => periodicFreeLoop (loops q) x) t -
        m62CurvatureVector F (fun y q => periodicFreeLoop (loops q) y) t x)) rampPeriod := by
  intro x
  let B (p : M) (v h : LoopAmbient) :=
    (F.metric t).tangentNorm p ((v : TangentSpace (𝓡 3) p) - h)
  change B (periodicFreeLoop (loops t) (x + rampPeriod))
      (curveVelocity (n := 3) (fun q => periodicFreeLoop (loops q) (x + rampPeriod)) t)
      (m62CurvatureVector F (fun y q => periodicFreeLoop (loops q) y) t (x + rampPeriod)) =
    B (periodicFreeLoop (loops t) x)
      (curveVelocity (n := 3) (fun q => periodicFreeLoop (loops q) x) t)
      (m62CurvatureVector F (fun y q => periodicFreeLoop (loops q) y) t x)
  rw [Proofs.M58.periodic_periodicFreeLoop (loops t) x]
  exact congrArg₂ (B (periodicFreeLoop (loops t) x))
    (time_velocity_periodic loops t x) (curvature_periodic F loops t x)

end PoincareConjecture.M65Perturbation
