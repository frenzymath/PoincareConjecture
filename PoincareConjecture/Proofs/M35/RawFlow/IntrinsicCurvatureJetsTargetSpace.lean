import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTarget
import PoincareConjecture.Proofs.M35.RadialGauge.RadialRapidProfile
import PoincareConjecture.Proofs.M35.RadialGauge.DilatedRapidProfile

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge

theorem raw_intrinsic_dilated_target_jets_bounded
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ eta : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (ht₀ : t₀ ∈ Icc 0 T) (heta : 0 ≤ eta) :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : EuclideanSpace ℝ (Fin 5), ∀ sigma,
      |sigma| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : EuclideanSpace ℝ (Fin 5) × ℝ =>
        smoothTargetCoupling (rawWarpingRadius P G hrotation t₀) ‖Real.exp p.2 • p.1‖)
          (x, sigma)‖ ≤ C := by
  have htG : t₀ ∈ Ico 0 G.lifetime := ⟨ht₀.1, ht₀.2.trans_lt hTlt⟩
  let f := rawWarpingRadius P G hrotation t₀
  have hf : ContDiff ℝ ∞ f := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have ho : Function.Odd f := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact intrinsicWarpingRadius_odd _ _ _
  have hscalar (j N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (smoothTargetCoupling f) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_target_jets_polynomial_decay P H G hrotation hT hTlt j N
    exact ⟨C, hC.le, fun r hr => hCb t₀ ht₀ r hr⟩
  have hEuclidean := even_radial_rapid_jets (E := EuclideanSpace ℝ (Fin 5))
    (smoothTargetCoupling_contDiff hf) (smoothTargetCoupling_even hf ho) hscalar
  have hfull := dilated_rapid_profile_jets_bounded
    (f := fun _ : Unit => fun x : EuclideanSpace ℝ (Fin 5) => smoothTargetCoupling f ‖x‖)
    heta (fun _ => smoothTargetCoupling_contDiff_norm hf ho)
    (fun j N => by
      obtain ⟨C, hC, hCb⟩ := hEuclidean j N
      exact ⟨C, hC, fun _ => hCb⟩)
  intro k
  obtain ⟨C, hC, hCb⟩ := hfull k
  exact ⟨C, hC, hCb ()⟩

end PoincareConjecture.M35.Uniqueness
