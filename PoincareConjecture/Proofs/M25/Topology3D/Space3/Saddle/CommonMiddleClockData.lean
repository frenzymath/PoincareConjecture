import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonRadialEvolution








set_option autoImplicit false

open Set Metric Function
open scoped ContDiff NNReal Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_saddle_common_middle_clock_data
    (e delta : ℝ) (he : 0 < e) (heSmall : e < 1 / 512)
    (hdelta : 0 < delta)
    (b : Fin 2 → ℝ × E2 → E2)
    (hb : ∀ j : Fin 2, ContDiff ℝ ∞ (b j))
    (P : Set E2) (hP : IsCompact P)
    (E : Fin 2 → ℝ → Set E2)
    (hExterior : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
      E j t ⊆ P ∩ {x : E2 | 1 ≤ ‖x‖})
    (hAnnulus : ∀ (j : Fin 2) (t : ℝ) (x : E2),
      |t| < 2 * delta → x ∈ E j t → ‖x‖ ≤ 1 + 3 * e →
        b 0 (t, x) = b j (t, x) ∧ ⟪x, b 0 (t, x)⟫_ℝ = 0) :
    ∃ (C : ℝ × E2 → E2) (W : Fin 2 → ℝ × E2 → E2)
      (K : Set E2)
      (hC : ContDiff ℝ ∞ C)
      (hsC : HasCompactSupport C)
      (hW : ∀ j : Fin 2, ContDiff ℝ ∞ (W j) ∧ HasCompactSupport (W j))
      (_hK : IsCompact K)
      (_hCs : tsupport C ⊆ Icc (-3 * delta) (3 * delta) ×ˢ K)
      (_hWs : ∀ j : Fin 2,
        tsupport (W j) ⊆ Icc (-3 * delta) (3 * delta) ×ˢ K)
      (_hRad : ∀ (t : ℝ) (x : E2), ⟪x, C (t, x)⟫_ℝ = 0)
      (_hCommon : ∀ (j : Fin 2) (t : ℝ) (x : E2), ‖x‖ ≤ 1 + 2 * e →
        W j (t, x) = C (t, x))
      (_hEq : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
        EqOn (fun x : E2 => W j (t, x)) (fun x => b j (t, x)) (E j t)),
      ∃ (KC LC : ℝ≥0) (KW LW : Fin 2 → ℝ≥0)
        (hKC : LipschitzWith KC (clockField C))
        (hLC : ∀ p : ℝ × E2, ‖clockField C p‖ ≤ LC)
        (hKW : ∀ j : Fin 2, LipschitzWith (KW j) (clockField (W j)))
        (hLW : ∀ (j : Fin 2) (p : ℝ × E2),
          ‖clockField (W j) p‖ ≤ LW j),
        let Psi : ℝ → ℝ →
            Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
          clockEvolutionDiffeomorph C hKC hLC hC hsC
        let Phi : Fin 2 → ℝ → ℝ →
            Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
          fun j => clockEvolutionDiffeomorph (W j) (hKW j) (hLW j)
            (hW j).1 (hW j).2
        let Kclock : Set E2 := (Prod.snd '' tsupport C) ∪
          ⋃ j : Fin 2, Prod.snd '' tsupport (W j)
        IsCompact Kclock ∧
        (∀ (s t : ℝ) (x : E2),
          Psi s t x = clockEvolution C hKC hLC s t x ∧
          (Psi s t).symm x = clockEvolution C hKC hLC t s x) ∧
        (∀ (j : Fin 2) (s t : ℝ) (x : E2),
          Phi j s t x = clockEvolution (W j) (hKW j) (hLW j) s t x ∧
          (Phi j s t).symm x = clockEvolution (W j) (hKW j) (hLW j) t s x) ∧
        (ContDiff ℝ ∞
            (fun p : (ℝ × ℝ) × E2 => Psi p.1.1 p.1.2 p.2) ∧
          ContDiff ℝ ∞
            (fun p : (ℝ × ℝ) × E2 => (Psi p.1.1 p.1.2).symm p.2)) ∧
        (∀ j : Fin 2,
          ContDiff ℝ ∞
            (fun p : (ℝ × ℝ) × E2 => Phi j p.1.1 p.1.2 p.2) ∧
          ContDiff ℝ ∞
            (fun p : (ℝ × ℝ) × E2 =>
              (Phi j p.1.1 p.1.2).symm p.2)) ∧
        (∀ (s t : ℝ) (x : E2),
          ‖Psi s t x‖ = ‖x‖ ∧ ‖(Psi s t).symm x‖ = ‖x‖) ∧
        (∀ (j : Fin 2) (s t : ℝ) (x : E2), ‖x‖ ≤ 1 + 2 * e →
          Phi j s t x = Psi s t x ∧
          (Phi j s t).symm x = (Psi s t).symm x) ∧
        (∀ s t : ℝ,
          tsupport (fun x : E2 => Psi s t x - x) ⊆ Kclock ∧
          tsupport (fun x : E2 => (Psi s t).symm x - x) ⊆ Kclock) ∧
        (∀ (j : Fin 2) (s t : ℝ),
          tsupport (fun x : E2 => Phi j s t x - x) ⊆ Kclock ∧
          tsupport (fun x : E2 => (Phi j s t).symm x - x) ⊆ Kclock) ∧
        (∀ (s t : ℝ) (x : E2), x ∉ Kclock →
          (Psi s t x = x ∧ (Psi s t).symm x = x) ∧
          ∀ j : Fin 2, Phi j s t x = x ∧ (Phi j s t).symm x = x) ∧
        (∀ (j : Fin 2) (s t a : ℝ), 0 ≤ a → a ≤ 1 + 2 * e →
          (Phi j s t) '' ball (0 : E2) a = ball (0 : E2) a ∧
          (Phi j s t).symm '' ball (0 : E2) a = ball (0 : E2) a ∧
          (Phi j s t) '' closedBall (0 : E2) a = closedBall (0 : E2) a ∧
          (Phi j s t).symm '' closedBall (0 : E2) a =
            closedBall (0 : E2) a ∧
          (Phi j s t) '' sphere (0 : E2) a = sphere (0 : E2) a ∧
          (Phi j s t).symm '' sphere (0 : E2) a = sphere (0 : E2) a) ∧
        (∀ (j : Fin 2) (s t : ℝ) (x : E2),
          HasDerivAt (fun u : ℝ => Phi j s u x)
            (W j (t, Phi j s t x)) t) ∧
        ∀ (j : Fin 2) (gamma : ℝ → E2) (a b s : ℝ), s ∈ Ioo a b →
          (∀ t ∈ Ioo a b,
            HasDerivAt gamma (W j (t, gamma t)) t) →
          EqOn (fun t : ℝ => Phi j s t (gamma s)) gamma (Ioo a b) := by
  rcases exists_saddle_common_radial_fields
      e delta he heSmall hdelta b hb P hP E hExterior hAnnulus with
    ⟨C, W, K, hC, hsC, hW, hK, hCs, hWs, hRad, hCommon, hEq⟩
  have hr : 0 < 1 + 2 * e := by linarith
  rcases exists_saddle_common_radial_evolution
      (1 + 2 * e) hr C hC hsC W hW hRad hCommon with
    ⟨KC, LC, KW, LW, hKC, hLC, hKW, hLW, hClock⟩
  exact ⟨C, W, K, hC, hsC, hW, hK, hCs, hWs, hRad, hCommon, hEq,
    KC, LC, KW, LW, hKC, hLC, hKW, hLW, hClock⟩

end PoincareConjecture.M25.Topology3D
