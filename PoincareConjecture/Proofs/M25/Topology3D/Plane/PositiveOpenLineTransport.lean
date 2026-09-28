import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenTubeTransport
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_positive_openLine_graph_transport
    (T : OpenPartialHomeomorph
      ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)))
    {U V K : Set (ℝ × ℝ)} (hV : IsOpen V) (hVU : V ⊆ U)
    (hK : IsCompact K) (hKV : K ⊆ V)
    {w A R : ℝ} (hA : 0 < A) (hAw : A < w) (hR : 0 < R)
    (hsource : T.source = U ×ˢ {q : ℝ × ℝ | |q.2| < w})
    (hparameter : ∀ p, (T p).1 = p.1)
    (hT : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (γ : (ℝ × ℝ) × ℝ → ℝ × ℝ) (hγ : ContDiff ℝ ∞ γ)
    (hnear : ∀ z ∈ V, ∀ u : ℝ, (z, γ (z, u)) ∈ T.target ∧
      0 < fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => (T.symm (p.1, γ p)).2.1)
        (z, u) (0, 1) ∧ |(T.symm (z, γ (z, u))).2.2| < A)
    (htail : ∀ z ∈ V, ∀ u : ℝ, R ≤ |u| →
      T.symm (z, γ (z, u)) = (z, (u, 0)))
    (τ : ℝ × ℝ → ℝ) (hτ : ContDiff ℝ ∞ τ)
    (hτBound : ∀ z, 0 ≤ τ z ∧ τ z ≤ 1) (hτZero : ∀ z, z ∉ K → τ z = 0) :
    ∃ F : (ℝ × ℝ) → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (F p.1).symm p.2) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → F z x = x ∧ (F z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x)) ∧
      (∀ z, (∀ u, γ (z, u) = (T (z, (u, 0))).2) →
        ∀ x, F z x = x ∧ (F z).symm x = x) ∧
      ∀ z ∈ V, τ z = 1 →
        range (fun u : ℝ => F z (T (z, (u, 0))).2) =
          range (fun u : ℝ => γ (z, u)) := by
  let H : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × (ℝ × ℝ) := fun p => (p.1, γ p)
  let ξ : (ℝ × ℝ) × ℝ → ℝ := fun p => (T.symm (H p)).2.1
  let η : (ℝ × ℝ) × ℝ → ℝ := fun p => (T.symm (H p)).2.2
  let D : (ℝ × ℝ) × ℝ → ℝ := fun p => fderiv ℝ ξ p (0, 1)
  have hcoords : ContDiffOn ℝ ∞ (fun p => T.symm (H p)) (V ×ˢ univ) :=
    hInv.comp (contDiff_fst.prodMk hγ).contDiffOn (fun p hp => (hnear p.1 hp.1 p.2).1)
  have hξ : ContDiffOn ℝ ∞ ξ (V ×ˢ univ) := hcoords.snd.fst
  have hη : ContDiffOn ℝ ∞ η (V ×ˢ univ) := hcoords.snd.snd
  have hder (z : ℝ × ℝ) (hz : z ∈ V) (u : ℝ) :
      HasDerivAt (fun v => ξ (z, v)) (D (z, u)) u :=
    hasDerivAt_fiber ((hξ.contDiffAt ((hV.prod isOpen_univ).mem_nhds
      ⟨hz, mem_univ _⟩)).differentiableAt (by simp)).hasFDerivAt
  have hcutoff (f : (ℝ × ℝ) × ℝ → ℝ)
      (hf : ContDiffOn ℝ ∞ f (V ×ˢ univ)) :
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => τ p.1 * f p) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.1 ∈ V
    · exact (hτ.comp contDiff_fst).contDiffAt.mul
        (hf.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))
    · have hpK : p.1 ∉ K := fun h => hp (hKV h)
      have hn : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 p, q.1 ∉ K :=
        (hK.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpK
      have hconst : ContDiffAt ℝ ∞ (fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) p :=
        contDiffAt_const
      apply hconst.congr_of_eventuallyEq
      filter_upwards [hn] with q hq
      simp only [hτZero q.1 hq, zero_mul]
  let P : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 + τ p.1 * (ξ p - p.2)
  have hP : ContDiff ℝ ∞ P :=
    contDiff_snd.add (hcutoff (fun p => ξ p - p.2) (hξ.sub contDiffOn_snd))
  have hPid (z : ℝ × ℝ) (hz : z ∉ V) (u : ℝ) : P (z, u) = u := by
    simp only [P, hτZero z (fun h => hz (hKV h)), zero_mul, add_zero]
  have hPtail (z : ℝ × ℝ) (u : ℝ) (hu : R ≤ |u|) : P (z, u) = u := by
    by_cases hz : z ∈ V
    · have hξtail : ξ (z, u) = u := congrArg (fun p => p.2.1) (htail z hz u hu)
      simp only [P, hξtail, sub_self, mul_zero, add_zero]
    · exact hPid z hz u
  have hPpos (z : ℝ × ℝ) (u : ℝ) : 0 < deriv (fun v => P (z, v)) u := by
    by_cases hz : z ∈ V
    · have hdP : HasDerivAt (fun v => P (z, v))
          (1 + τ z * (D (z, u) - 1)) u := by
        convert! (hasDerivAt_id u).add (((hder z hz u).sub (hasDerivAt_id u)).const_mul (τ z))
      rw [hdP.deriv]
      convert lineInterpolation_derivative_pos (hnear z hz u).2.1 (hτBound z) using 1
      ring
    · have heq : (fun v => P (z, v)) = id := funext (hPid z hz)
      rw [heq, deriv_id]
      exact zero_lt_one
  have hPsurj (z : ℝ × ℝ) : Surjective (fun u => P (z, u)) := by
    apply surjective_of_eq_self_outside_interval
      (hP.continuous.comp (continuous_const.prodMk continuous_id)) (-R) R
    intro u hu
    apply hPtail
    rcases hu with hl | hr
    · exact (by linarith : R ≤ -u).trans (neg_le_abs u)
    · exact hr.trans (le_abs_self u)
  let Dfull := fiberDiffeomorph hP hPpos hPsurj
  have hDfull (p : (ℝ × ℝ) × ℝ) : Dfull p = (p.1, P p) :=
    fiberDiffeomorph_apply hP hPpos hPsurj p
  have hDinvparam (p : (ℝ × ℝ) × ℝ) : (Dfull.symm p).1 = p.1 := by
    have h := congrArg Prod.fst (Dfull.apply_symm_apply p)
    simpa only [hDfull] using h
  let G : (ℝ × ℝ) × ℝ → ℝ := fun p => (Dfull.symm p).2
  have hG : ContDiff ℝ ∞ G := Dfull.symm.contDiff.snd
  have hGleft (z : ℝ × ℝ) (u : ℝ) : P (z, G (z, u)) = u := by
    have h := congrArg Prod.snd (Dfull.apply_symm_apply (z, u))
    rw [hDfull] at h
    have hp : Dfull.symm (z, u) = (z, G (z, u)) := Prod.ext (hDinvparam _) rfl
    rw [hp] at h
    exact h
  have hGright (z : ℝ × ℝ) (u : ℝ) : G (z, P (z, u)) = u := by
    have h := congrArg Prod.snd (Dfull.symm_apply_apply (z, u))
    rw [hDfull] at h
    exact h
  have hGtail (z : ℝ × ℝ) (u : ℝ) (hu : R ≤ |u|) : G (z, u) = u := by
    simpa only [hPtail z u hu] using hGright z u
  let g : (ℝ × ℝ) × ℝ → ℝ := fun p => τ p.1 * η (p.1, G p)
  have hg : ContDiff ℝ ∞ g := hcutoff (fun p => η (p.1, G p))
    (hη.comp (contDiff_fst.prodMk hG).contDiffOn (fun _ hp => ⟨hp.1, mem_univ _⟩))
  have hgBound (p : (ℝ × ℝ) × ℝ) : |g p| < A := by
    by_cases hz : p.1 ∈ V
    · simp only [g, abs_mul, abs_of_nonneg (hτBound p.1).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hτBound p.1).2).trans_lt
        (hnear p.1 hz (G p)).2.2
    · simp only [g, hτZero p.1 (fun h => hz (hKV h)), zero_mul, abs_zero]
      exact hA
  have hgZero (z : ℝ × ℝ) (u : ℝ) (hu : z ∉ K ∨ R ≤ |u|) : g (z, u) = 0 := by
    rcases hu with hz | hu
    · simp only [g, hτZero z hz, zero_mul]
    · by_cases hz : z ∈ V
      · have hηtail : η (z, u) = 0 := congrArg (fun p => p.2.2) (htail z hz u hu)
        simp only [g, hGtail z u hu, hηtail, mul_zero]
      · simp only [g, hτZero z (fun h => hz (hKV h)), zero_mul]
  obtain ⟨F, hF, hFi, hQ, hSupport, hStationary, hGraph⟩ :=
    exists_relative_openTube_graph_transport T hK (fun _ hz => hVU (hKV hz)) hA hAw hR
      hsource hparameter hT hInv g hg hgBound hgZero
  refine ⟨F, hF, hFi, hQ, hSupport, ?_, ?_⟩
  · intro z hstat x
    apply hStationary z ?_ x
    intro u
    by_cases hz : z ∈ V
    · have hs : (z, (G (z, u), (0 : ℝ))) ∈ T.source := by
        rw [hsource]
        exact ⟨hVU hz, by change |(0 : ℝ)| < w; simpa using hA.trans hAw⟩
      have hf : H (z, G (z, u)) = T (z, (G (z, u), 0)) :=
        Prod.ext (hparameter (z, (G (z, u), 0))).symm (hstat _)
      have he : η (z, G (z, u)) = 0 := by
        dsimp only [η]
        rw [hf, T.left_inv hs]
      simp only [g, he, mul_zero]
    · exact hgZero z u (Or.inl (fun h => hz (hKV h)))
  · intro z hz hτone
    have hPξ (v : ℝ) : P (z, v) = ξ (z, v) := by
      dsimp only [P]
      rw [hτone]
      ring
    have haction (u : ℝ) : F z (T (z, (u, 0))).2 = γ (z, G (z, u)) := by
      have hp : H (z, G (z, u)) ∈ T.target := (hnear z hz _).1
      have hparamInv : (T.symm (H (z, G (z, u)))).1 = z := by
        have h := congrArg Prod.fst (T.right_inv hp)
        simpa only [hparameter, H] using h
      have hξG : ξ (z, G (z, u)) = u := by
        rw [← hPξ]
        exact hGleft z u
      have hgin : g (z, u) = η (z, G (z, u)) := by
        simp only [g, hτone, one_mul]
      have hinv : T.symm (H (z, G (z, u))) = (z, (u, g (z, u))) :=
        Prod.ext hparamInv (Prod.ext hξG hgin.symm)
      have hout : (T (z, (u, g (z, u)))).2 = γ (z, G (z, u)) := by
        rw [← hinv]
        exact congrArg Prod.snd (T.right_inv hp)
      exact (hGraph z (hVU hz) u).trans hout
    apply Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨G (z, u), (haction u).symm⟩
    · rintro _ ⟨u, rfl⟩
      refine ⟨P (z, u), ?_⟩
      change F z (T (z, (P (z, u), 0))).2 = γ (z, u)
      rw [haction, hGright]

end PoincareConjecture.M25.Topology3D
