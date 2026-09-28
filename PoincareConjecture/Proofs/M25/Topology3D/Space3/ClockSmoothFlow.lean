import PoincareConjecture.Proofs.M25.Topology3D.Space3.AffineFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowInvariants

set_option autoImplicit false

open scoped ContDiff NNReal Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clockField_contDiff (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (clockField V) := contDiff_const.prodMk hV

omit [NormedSpace ℝ E] in

theorem clockField_compact_perturbation (V : ℝ × E → E) (hs : HasCompactSupport V) :
    HasCompactSupport (fun p => clockField V p - (1, (0 : E))) := by
  apply hs.mono
  intro p hp hz
  exact hp (by simp only [clockField, hz, sub_self])

theorem clockField_bounds (V : ℝ × E → E) (hV : ContDiff ℝ ∞ V)
    (hs : HasCompactSupport V) :
    ∃ K L : ℝ≥0, LipschitzWith K (clockField V) ∧ ∀ p, ‖clockField V p‖ ≤ L := by
  let c : ℝ × E := (1, 0)
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds (fun p => clockField V p - c)
    ((clockField_contDiff V hV).sub contDiff_const) (clockField_compact_perturbation V hs)
  refine ⟨K, L + ‖c‖₊, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hK.dist_le_mul p q
  · intro p
    change ‖clockField V p‖ ≤ (L : ℝ) + ‖c‖
    linarith [norm_le_norm_sub_add (clockField V p) c, hL p]

variable [FiniteDimensional ℝ E]
variable (V : ℝ × E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)

theorem boundedClockFlow_contDiff (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V) :
    ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ => boundedFlow (clockField V) hK hL p.1 p.2) :=
  boundedFlow_contDiff_of_compact_perturbation (clockField V) hK hL
    (clockField_contDiff V hV) (1, 0) (clockField_compact_perturbation V hs)

theorem clockEvolution_contDiff (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E => clockEvolution V hK hL p.1.1 p.1.2 p.2) := by
  have hparam : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E =>
      ((p.1.1, p.2), p.1.2 - p.1.1)) :=
    (contDiff_fst.fst.prodMk contDiff_snd).prodMk (contDiff_fst.snd.sub contDiff_fst.fst)
  simpa only [clockEvolution, Function.comp_def] using
    ((boundedClockFlow_contDiff V hK hL hV hs).comp hparam).snd

noncomputable def clockEvolutionDiffeomorph (hV : ContDiff ℝ ∞ V)
    (hs : HasCompactSupport V) (s t : ℝ) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toEquiv := clockEvolutionEquiv V hK hL s t
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x => clockEvolution V hK hL s t x)
    exact ((clockEvolution_contDiff V hK hL hV hs).comp
      ((contDiff_const (c := (s, t))).prodMk contDiff_id)).contMDiff
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x => clockEvolution V hK hL t s x)
    exact ((clockEvolution_contDiff V hK hL hV hs).comp
      ((contDiff_const (c := (t, s))).prodMk contDiff_id)).contMDiff

theorem clockEvolution_preserves_height
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (W : ℝ × (H × ℝ) → H × ℝ) {K L : ℝ≥0}
    (hK : LipschitzWith K (clockField W)) (hL : ∀ p, ‖clockField W p‖ ≤ L)
    (hz : ∀ p, (W p).2 = 0) (s t : ℝ) (x : H × ℝ) :
    (clockEvolution W hK hL s t x).2 = x.2 := by
  let A : (ℝ × (H × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ H ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (H × ℝ))
  exact boundedFlow_preserves_linear (clockField W) hK hL A hz (s, x) (t - s)

end PoincareConjecture.M25.Topology3D
