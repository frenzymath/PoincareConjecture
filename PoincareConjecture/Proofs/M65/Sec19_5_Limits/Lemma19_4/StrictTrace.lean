import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceFiniteBranches
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceInjective
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.Attainment

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {N : ℕ}

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

end PoincareConjecture
