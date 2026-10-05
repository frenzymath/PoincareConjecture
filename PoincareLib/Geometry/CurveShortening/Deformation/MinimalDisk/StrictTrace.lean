import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.StrictTraceFiniteBranches
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.StrictTraceInjective
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Attainment

/-!
# The actual Plateau strict-trace input

The shared Hartman--Wintner theorem produces finite actual branches.
The true within differential then excludes collapsed weak boundary
arcs, giving the literal circle homeomorphism. This discharges the
frozen strict-trace input without changing any of its quantifiers.
Source: M65 derivations 41 and 43, for Heinz 1970, pp. 99--105,
and Morgan--Tian Lemma 19.2, pp. 438--439.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace PoincareMT

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {N : ℕ}

/-- The actual smooth regular Jordan loop and the given regular harmonic
conformal representative supply the exact fifth attainment input.
Neither a strict parameter nor finite branches are assumed. Source:
MT Lemma 19.2, pp. 438--439; derivation 43, shared Hartman--Wintner consumer. -/
theorem m65Plateau_strict_trace
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (hei : Function.Injective e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (gamma : C1FreeLoopSpace (M := M))
    (hgamma : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    (a b c : LoopCircle) :
    M65PlateauStrictTraceInput g D e gamma a b c := by
  intro F _hmin hconf f hf hb htrace
  have hc := m65Attainment_conformal F he hinj hf hconf
  have hfinite := M65StrictTrace.finite_disk_branches D he hei hf.smooth hb hc hf.harmonic
    gamma.continuous hgamma hsmooth hregular F.weakly_monotone.surjective htrace
  have hi := M65StrictTrace.parameter_injective_of_finite_branches hb hc F.parameter
    F.weakly_monotone htrace hfinite
  let E := Equiv.ofBijective F.parameter ⟨hi, F.weakly_monotone.surjective⟩
  let beta : LoopCircle ≃ₜ LoopCircle :=
    Continuous.homeoOfEquivCompactToT2 (f := E) F.parameter.continuous
  exact ⟨beta, fun _ => rfl, hfinite⟩

end PoincareMT
