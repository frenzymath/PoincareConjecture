import PoincareConjecture.Proofs.M09.SmoothSquarePath
import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Definitions.Ch06.ReducedLength

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem exists_lVariation_of_smoothSquareFamily
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ) (hI : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ U)
    (hcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (s, 0) = A.squareFamily Z s) :
    ∃ V : LVariation F T 0 b (A.path Z b hb hmax),
      V.radius = ρ ∧ (∀ s u, V.squareFamily s u = f (s, u)) ∧
      (∀ u, Set.EqOn (fun t ↦ V.family t u) (fun t ↦ f (Real.sqrt t, u)) (Set.Icc 0 b)) ∧
      ∀ u, variationLLength V u = backwardLLength F T 0 b (fun t ↦ f (Real.sqrt t, u)) := by
  classical
  let P := A.path Z b hb hmax
  let family : ℝ → ℝ → M := fun t u ↦ if u = 0 then P.curve t else f (Real.sqrt t, u)
  have heq (u : ℝ) : Set.EqOn (fun t ↦ family t u) (fun t ↦ f (Real.sqrt t, u)) (Set.Icc 0 b) := by
    intro t ht
    by_cases hu : u = 0
    · subst u
      simp only [family, if_pos rfl]
      have hs : Real.sqrt t ∈ Set.Icc 0 (Real.sqrt b) :=
        ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩
      have h := (hcenter (Real.sqrt t) hs).trans (A.square_agrees Z (Real.sqrt t)
        ⟨hs.1, hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩)
      rw [Real.sq_sqrt ht.1] at h
      exact (congrFun (A.path_eq Z b hb hmax) t).trans h.symm
    · simp only [family, if_neg hu]
  let V : LVariation F T 0 b P := {
    family := family
    at_zero := fun t ↦ by simp only [family, if_pos rfl]
    radius := ρ
    radius_pos := hρ
    squareFamily := fun s u ↦ f (s, u)
    squareDomain := U
    square_open := hU
    square_contains := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hI
    square_smooth := hf
    square_agrees := by
      intro s hs u _
      have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
      have hsB : s ^ 2 ≤ b := by
        have h := mul_self_le_mul_self hs0 hs.2
        simpa only [← pow_two, Real.sq_sqrt hb.le] using h
      have h := heq u (show s ^ 2 ∈ Set.Icc 0 b from ⟨sq_nonneg s, hsB⟩)
      simpa only [Real.sqrt_sq hs0] using h.symm
    l_integrable := by
      intro u hu
      by_cases hu0 : u = 0
      · subst u
        simpa only [family, if_pos rfl] using P.l_integrable
      · let D := (fun s : ℝ ↦ (s, u)) ⁻¹' U
        have hD : IsOpen D := hU.preimage (continuous_id.prodMk continuous_const)
        have hDI : Set.Icc 0 (Real.sqrt b) ⊆ D := fun s hs ↦ hI ⟨hs, hu⟩
        have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s ↦ f (s, u)) D :=
          hf.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
        obtain ⟨Q, hQ, _⟩ := exists_backwardPath_of_smoothSquareCurve F hM04 T τmax hτmax hwindow
          b hb hmax (fun s ↦ f (s, u)) D hD hDI hα
        have hi := Q.l_integrable
        rw [hQ] at hi
        simpa only [family, if_neg hu0] using hi
  }
  refine ⟨V, rfl, fun _ _ ↦ rfl, heq, ?_⟩
  intro u
  exact backwardLLength_congr_Ioo F T 0 b hb.le _ _ ((heq u).mono Set.Ioo_subset_Icc_self)

theorem exists_initialFixedLVariation_of_smoothSquareFamily
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ) (hI : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ U)
    (hcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (s, 0) = A.squareFamily Z s)
    (hleft : ∀ u ∈ Set.Ioo (-ρ) ρ, f (0, u) = f (0, 0)) :
    ∃ V : InitialFixedLVariation F T 0 b (A.path Z b hb hmax),
      V.radius = ρ ∧ (∀ s u, V.squareFamily s u = f (s, u)) ∧
      (∀ u, Set.EqOn (fun t ↦ V.family t u) (fun t ↦ f (Real.sqrt t, u)) (Set.Icc 0 b)) ∧
      ∀ u, variationLLength V.toLVariation u = backwardLLength F T 0 b (fun t ↦ f (Real.sqrt t, u)) := by
  obtain ⟨V, hVr, hVf, hVeq, hVa⟩ := exists_lVariation_of_smoothSquareFamily
    hM04 hτmax hwindow A Z b hb hmax f U hU hf ρ hρ hI hcenter
  have hfix : ∀ u ∈ Set.Ioo (-V.radius) V.radius, V.family 0 u = (A.path Z b hb hmax).curve 0 := by
    intro u hu
    have hu' : u ∈ Set.Ioo (-ρ) ρ := by simpa only [hVr] using hu
    have h1 := hVeq u (show (0 : ℝ) ∈ Set.Icc 0 b from ⟨le_rfl, hb.le⟩)
    have h0 := hVeq 0 (show (0 : ℝ) ∈ Set.Icc 0 b from ⟨le_rfl, hb.le⟩)
    dsimp only at h1 h0
    rw [Real.sqrt_zero, hleft u hu'] at h1
    rw [Real.sqrt_zero, V.at_zero] at h0
    exact h1.trans h0.symm
  exact ⟨{ toLVariation := V, fixed_left := hfix }, hVr, hVf, hVeq, hVa⟩

theorem exists_fixedEndpointLVariation_of_smoothSquareFamily
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ) (hI : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ U)
    (hcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (s, 0) = A.squareFamily Z s)
    (hleft : ∀ u ∈ Set.Ioo (-ρ) ρ, f (0, u) = f (0, 0))
    (hright : ∀ u ∈ Set.Ioo (-ρ) ρ, f (Real.sqrt b, u) = f (Real.sqrt b, 0)) :
    ∃ V : FixedEndpointLVariation F T 0 b (A.path Z b hb hmax),
      V.radius = ρ ∧ (∀ s u, V.squareFamily s u = f (s, u)) ∧
      (∀ u, Set.EqOn (fun t ↦ V.family t u) (fun t ↦ f (Real.sqrt t, u)) (Set.Icc 0 b)) ∧
      ∀ u, variationLLength V.toLVariation u = backwardLLength F T 0 b (fun t ↦ f (Real.sqrt t, u)) := by
  obtain ⟨V, hVr, hVf, hVeq, hVa⟩ := exists_initialFixedLVariation_of_smoothSquareFamily
    hM04 hτmax hwindow A Z b hb hmax f U hU hf ρ hρ hI hcenter hleft
  have hfix : ∀ u ∈ Set.Ioo (-V.radius) V.radius, V.family b u = (A.path Z b hb hmax).curve b := by
    intro u hu
    have hu' : u ∈ Set.Ioo (-ρ) ρ := by simpa only [hVr] using hu
    have h1 := hVeq u (show b ∈ Set.Icc 0 b from ⟨hb.le, le_rfl⟩)
    have h0 := hVeq 0 (show b ∈ Set.Icc 0 b from ⟨hb.le, le_rfl⟩)
    dsimp only at h1 h0
    rw [hright u hu'] at h1
    rw [V.at_zero] at h0
    exact h1.trans h0.symm
  exact ⟨{ toInitialFixedLVariation := V, fixed_right := hfix }, hVr, hVf, hVeq, hVa⟩

end PoincareConjecture.Proofs.M09
