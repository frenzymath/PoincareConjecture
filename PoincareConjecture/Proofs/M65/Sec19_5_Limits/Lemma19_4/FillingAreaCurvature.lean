import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaBoundaryLength
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Filling

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

def loopCurvature {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (gamma : C1FreeLoopSpace (M := M)) (x : ℝ) :
    TangentSpace (𝓡 3) (periodicFreeLoop gamma x) :=
  (g.tangentNorm (periodicFreeLoop gamma x)
    (curveVelocity (n := 3) (periodicFreeLoop gamma) x))⁻¹ •
    rampHorizontalCovariantDerivative D (periodicFreeLoop gamma)
      (fun y => (g.tangentNorm (periodicFreeLoop gamma y)
        (curveVelocity (n := 3) (periodicFreeLoop gamma) y))⁻¹ •
        curveVelocity (n := 3) (periodicFreeLoop gamma) y) x

private theorem loopCurvature_periodic {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (gamma : C1FreeLoopSpace (M := M)) :
    Function.Periodic (fun x => (loopCurvature D gamma x : LoopAmbient)) rampPeriod := by
  let c := periodicFreeLoop gamma
  have hp : Function.Periodic c rampPeriod := Proofs.M58.periodic_periodicFreeLoop gamma
  have hv : Function.Periodic (fun x => (curveVelocity (n := 3) c x : LoopAmbient))
      rampPeriod := by
    intro x
    have hh := m65CurveVelocity_comp (gamma := c) (phi := fun y => y + rampPeriod) (x := x)
      ((Proofs.M58.contMDiff_periodicFreeLoop gamma (x + rampPeriod)).mdifferentiableAt
        one_ne_zero) ((hasDerivAt_id x).add_const rampPeriod)
    have he : c ∘ (fun y => y + rampPeriod) = c := funext hp
    have hh0 : (curveVelocity (n := 3) c (x + rampPeriod) : LoopAmbient) =
        (curveVelocity (n := 3) (c ∘ (fun y => y + rampPeriod)) x : LoopAmbient) := by
      simpa only [one_smul] using hh.symm
    exact hh0.trans (congrArg (fun f : ℝ → M => (curveVelocity (n := 3) f x : LoopAmbient)) he)
  let speed := fun x => g.tangentNorm (c x) (curveVelocity (n := 3) c x)
  have hs : Function.Periodic speed rampPeriod := Proofs.M58.periodic_freeLoopSpeed g gamma
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
    rampHorizontalCovariantDerivative D c Y (x + rampPeriod) =
      (speed x)⁻¹ • rampHorizontalCovariantDerivative D c Y x
  rw [hs x]
  congr 1
  let B (p : M) (y w : LoopAmbient) (s : ℝ) : LoopAmbient :=
    let ep := trivializationAt LoopAmbient (TangentSpace (𝓡 3) : M → Type _) p
    ep.symmL ℝ p (deriv (fun z => (ep ⟨c z, Y z⟩).2) s) +
      D.connection (FiberBundle.extend LoopAmbient (x := p) (y : TangentSpace (𝓡 3) p)) p
        (w : TangentSpace (𝓡 3) p)
  change B (c (x + rampPeriod)) (Y (x + rampPeriod)) (curveVelocity c (x + rampPeriod))
      (x + rampPeriod) = B (c x) (Y x) (curveVelocity c x) x
  exact (congrArg (fun p => B p (Y (x + rampPeriod))
    (curveVelocity c (x + rampPeriod)) (x + rampPeriod)) (hp x)).trans
    ((congrArg₂ (fun y w : LoopAmbient => B (c x) y w (x + rampPeriod))
      (hY x) (hv x)).trans
      (congrArg (fun w => (e.symmL ℝ (c x) w +
        D.connection (FiberBundle.extend LoopAmbient (Y x)) (c x) (curveVelocity c x) :
          LoopAmbient)) hd))

theorem exists_curvature_section {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (gamma : C1FreeLoopSpace (M := M)) (hinj : Function.Injective (gamma : LoopCircle → M)) :
    ∃ H : (p : M) → TangentSpace (𝓡 3) p,
      ∀ x : ℝ, H (periodicFreeLoop gamma x) = loopCurvature D gamma x := by
  classical
  have hsame (x y : ℝ) (he : periodicFreeLoop gamma x = periodicFreeLoop gamma y) :
      loopCurvature D gamma x = loopCurvature D gamma y := by
    have hangle : m65LoopAngular x = m65LoopAngular y := by
      apply hinj
      rw [← gamma.boundary (m65LoopAngular x), ← gamma.boundary (m65LoopAngular y)]
      exact he
    unfold m65LoopAngular at hangle
    rw [← m65AngleLoopCircle_coe x, ← m65AngleLoopCircle_coe y] at hangle
    have hexp : Circle.exp x = Circle.exp y :=
      congrArg AddCircle.homeomorphCircle' (m65AngleLoopCircle.injective hangle)
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp
    have hk' : x = y + (k : ℝ) * rampPeriod := by simpa only [rampPeriod] using hk
    rw [hk']
    exact (loopCurvature_periodic D gamma).int_mul k y
  let H : (p : M) → TangentSpace (𝓡 3) p := fun p =>
    if hp : ∃ x : ℝ, periodicFreeLoop gamma x = p then
      loopCurvature D gamma (Classical.choose hp) else 0
  refine ⟨H, ?_⟩
  intro x
  have hp : ∃ y : ℝ, periodicFreeLoop gamma y = periodicFreeLoop gamma x := ⟨x, rfl⟩
  dsimp only [H]
  rw [dif_pos hp]
  exact hsame _ x (Classical.choose_spec hp)

end PoincareConjecture.M65Filling
