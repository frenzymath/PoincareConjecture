import PoincareConjecture.Proofs.M76.Mathlib.FlexiblePlanarQuarterTurn
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd












set_option autoImplicit false

open Set Geometry

namespace AddCircle






theorem exists_supported_cylinder_quarterTurn_of_lt (p : ℝ) [Fact (0 < p)] (hp : 4 < p)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR1 : R < 1) :
    ∃ F : (AddCircle p × ℝ) ≃ₜ (AddCircle p × ℝ),
      (∀ s : ℝ, |s| ≤ r → ∀ t : ℝ, |t| ≤ r →
        F ((s : AddCircle p), t) = (((-t : ℝ) : AddCircle p), s)) ∧
      (∀ s : ℝ, |s| ≤ r → ∀ t : ℝ, |t| ≤ r →
        F.symm ((s : AddCircle p), t) = ((t : AddCircle p), -s)) ∧
      (∀ z : AddCircle p × ℝ, R ≤ |z.2| → F z = z) ∧
      MapsTo F (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo F.symm (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      ∀ a b : ℝ,
        let A := (openPartialHomeomorphCoe p a).prod (OpenPartialHomeomorph.refl ℝ)
        let B := (openPartialHomeomorphCoe p b).prod (OpenPartialHomeomorph.refl ℝ)
        A.trans (F.toOpenPartialHomeomorph.trans B.symm) ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
  let q := shortArcQuotient p 2
  let Q := q.prod (OpenPartialHomeomorph.refl ℝ)
  let K := {z : ℝ × ℝ | ‖z‖ ≤ R}
  have hqS : q.source = Ioo (-2) 2 := shortArcQuotient_source p (by linarith)
  have hK : IsCompact K := by
    simpa only [K, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : ℝ × ℝ) R
  have hKS : K ⊆ Q.source := by
    intro z hz
    refine ⟨?_, mem_univ _⟩
    rw [hqS]
    have hx : |z.1| ≤ R := (norm_fst_le z).trans hz
    constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  obtain ⟨H, hHPL, hHcore, hHfix⟩ :=
    SupportedPlanarShear.exists_quarterTurn_homeomorph_of_lt hr hrR
  have hHout : EqOn H id Kᶜ := by
    intro z hz
    exact hHfix z (le_of_lt (lt_of_not_ge hz))
  obtain ⟨F, hFQ, hFout⟩ := Q.exists_supported_chart_homeomorph H hK hKS hHout
  have hcore (s : ℝ) (hs : |s| ≤ r) (t : ℝ) (ht : |t| ≤ r) :
      F ((s : AddCircle p), t) = (((-t : ℝ) : AddCircle p), s) := by
    have hzQ : (s, t) ∈ Q.source := by
      refine ⟨?_, mem_univ _⟩
      rw [hqS]
      constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    change F (Q (s, t)) = (((-t : ℝ) : AddCircle p), s)
    rw [hFQ (Q.map_source hzQ)]
    change Q (H (Q.symm (Q (s, t)))) = (((-t : ℝ) : AddCircle p), s)
    rw [Q.left_inv hzQ, hHcore (s, t) (by
      simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using And.intro hs ht)]
    rfl
  have hheight (z : AddCircle p × ℝ) (hz : R ≤ |z.2|) : F z = z := by
    by_cases hzQ : z ∈ Q.target
    · rw [hFQ hzQ]
      change Q (H (Q.symm z)) = z
      have hnorm : R ≤ ‖Q.symm z‖ :=
        hz.trans (show |z.2| ≤ ‖Q.symm z‖ from norm_snd_le (Q.symm z))
      rw [hHfix (Q.symm z) hnorm, Q.right_inv hzQ]
    · apply hFout
      rintro ⟨x, hx, rfl⟩
      exact hzQ (Q.map_source (hKS hx))
  have hinvheight (z : AddCircle p × ℝ) (hz : R ≤ |z.2|) : F.symm z = z := by
    apply F.injective
    rw [F.apply_symm_apply, hheight z hz]
  have hpres (G : (AddCircle p × ℝ) ≃ₜ (AddCircle p × ℝ))
      (hG : ∀ z : AddCircle p × ℝ, R ≤ |z.2| → G z = z) :
      MapsTo G (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    by_contra hn
    have hbound : 1 ≤ |(G z).2| := le_of_not_gt (fun h => hn (abs_lt.mp h))
    have he : G z = z := G.injective (hG (G z) (by linarith))
    exact hn (he.symm ▸ hz.2)
  refine ⟨F, hcore, ?_, hheight, hpres F hheight, hpres F.symm hinvheight, ?_⟩
  · intro s hs t ht
    apply F.injective
    rw [F.apply_symm_apply, hcore t ht (-s) (by simpa only [abs_neg] using hs)]
    simp only [neg_neg]
  · intro a b
    let A := (openPartialHomeomorphCoe p a).prod (OpenPartialHomeomorph.refl ℝ)
    let B := (openPartialHomeomorphCoe p b).prod (OpenPartialHomeomorph.refl ℝ)
    have hAQ : A.trans Q.symm ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
      dsimp only [A, Q]
      rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans,
        OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.trans_refl]
      exact piecewiseAffineGroupoid_prod _ _
        (shortArcQuotient_transition_mem_piecewiseAffineGroupoid p 2 a)
        (piecewiseAffineGroupoid ℝ).id_mem
    have hBQ : B.trans Q.symm ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
      dsimp only [B, Q]
      rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans,
        OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.trans_refl]
      exact piecewiseAffineGroupoid_prod _ _
        (shortArcQuotient_transition_mem_piecewiseAffineGroupoid p 2 b)
        (piecewiseAffineGroupoid ℝ).id_mem
    have hAB : A.trans B.symm ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
      dsimp only [A, B]
      rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans,
        OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.trans_refl]
      exact piecewiseAffineGroupoid_prod _ _
        (quotient_chart_transition_mem_piecewiseAffineGroupoid p a b)
        (piecewiseAffineGroupoid ℝ).id_mem
    exact Q.supported_chart_transition_mem_piecewiseAffineGroupoid A B H F
      hK hKS hHout hFQ hFout hHPL hAQ hBQ hAB





theorem exists_supported_cylinder_quarterTurn (p : ℝ) [Fact (0 < p)] (hp : 4 < p) :
    ∃ F : (AddCircle p × ℝ) ≃ₜ (AddCircle p × ℝ),
      (∀ s : ℝ, |s| ≤ 1 / 2 → ∀ t : ℝ, |t| ≤ 1 / 2 →
        F ((s : AddCircle p), t) = (((-t : ℝ) : AddCircle p), s)) ∧
      (∀ s : ℝ, |s| ≤ 1 / 2 → ∀ t : ℝ, |t| ≤ 1 / 2 →
        F.symm ((s : AddCircle p), t) = ((t : AddCircle p), -s)) ∧
      (∀ z : AddCircle p × ℝ, 3 / 4 ≤ |z.2| → F z = z) ∧
      MapsTo F (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo F.symm (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      ∀ a b : ℝ,
        let A := (openPartialHomeomorphCoe p a).prod (OpenPartialHomeomorph.refl ℝ)
        let B := (openPartialHomeomorphCoe p b).prod (OpenPartialHomeomorph.refl ℝ)
        A.trans (F.toOpenPartialHomeomorph.trans B.symm) ∈ piecewiseAffineGroupoid (ℝ × ℝ) :=
  exists_supported_cylinder_quarterTurn_of_lt p hp (by norm_num) (by norm_num) (by norm_num)

end AddCircle
