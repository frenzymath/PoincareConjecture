import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcAffineRounding
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcTubeHomotopy

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_affine_rounded_openArc_transport {n : ℕ} (a h : ℝ) (hh : 0 < h)
    (Φ : ℝ × ℝ → Polygon (ℝ × ℝ) (n + 2))
    (hΦ : ∀ k, ContDiff ℝ ∞ (fun z => Φ z k))
    (hgood : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      IsSimplePolygonalArc (Φ (s, t)) ∧ Φ (s, t) 0 = (a, 0) ∧
      Φ (s, t) (Fin.last (n + 1)) = (a + h * (n + 1 : ℕ), 0) ∧
      ∀ k, k ≠ 0 → k ≠ Fin.last (n + 1) →
        a < (Φ (s, t) k).1 ∧ (Φ (s, t) k).1 < a + h * (n + 1 : ℕ))
    (hmesh : ∀ s t, t ≤ 0 ∨ 1 ≤ t → ∀ k,
      Φ (s, t) k = (a + h * (k.val : ℝ), 0))
    (haxis : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k, (Φ (1, t) k).2 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ u, δ ≤ |u| → ρ u = |u|) ∧
      (∀ u, |u| ≤ ρ u ∧ ρ u ≤ |u| + δ) ∧ (∀ u, |deriv ρ u| ≤ 1) ∧
      ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (G p.1).symm p.2) ∧
        (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
          ∀ t x, x ∉ Q → G t x = x ∧ (G t).symm x = x) ∧
        (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, G t x = x ∧ (G t).symm x = x) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ,
          (G t (affineRoundedOpenArcParameter ρ a h (Φ (0, t)) u)).2 = 0 := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let p : (ℝ × ℝ) → Polygon (ℝ × ℝ) (n + 2) :=
    fun z => normalizeOpenArc a h (Φ (z.2, z.1))
  have hp (k : Fin (n + 2)) : ContDiff ℝ ∞ (fun z => p z k) :=
    (((hΦ k).comp (contDiff_snd.prodMk contDiff_fst)).sub contDiff_const).const_smul _
  have hpgood (z : ℝ × ℝ) (hz : z ∈ K) :
      IsSimplePolygonalArc (p z) ∧ p z 0 = (0, 0) ∧
      p z (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0) ∧
      ∀ k, k ≠ 0 → k ≠ Fin.last (n + 1) →
        0 < (p z k).1 ∧ (p z k).1 < (n + 1 : ℕ) := by
    obtain ⟨hsimple, h0, hN, hstrip⟩ := hgood z.2 hz.2 z.1 hz.1
    exact normalizeOpenArc_good hh (Φ (z.2, z.1)) hsimple h0 hN hstrip
  obtain ⟨δ, hδ, hδquarter, ρ, hρ, hρtail, hρbound, hρder, hE,
      hEinj, hEreg, hEtail, _, hEid, hEaxis⟩ :=
    exists_smooth_rounded_openArc_family (isCompact_Icc.prod isCompact_Icc)
      p hp hpgood (ε := 1) (by norm_num)
  let E : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun x => roundedOpenArcParameter ρ (p x.1) x.2
  let D : (ℝ × ℝ) × ℝ → ℝ × ℝ :=
    fun x => (a, 0) + h • E (x.1, (x.2 - a) / h)
  change ContDiff ℝ ∞ E at hE
  have hD : ContDiff ℝ ∞ D :=
    contDiff_const.add ((hE.comp
      (contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const h))).const_smul h)
  have hDinj (z : ℝ × ℝ) (hz : z ∈ K) : Injective (fun u : ℝ => D (z, u)) := by
    intro u v huv
    have heq : E (z, (u - a) / h) = E (z, (v - a) / h) :=
      smul_right_injective (ℝ × ℝ) hh.ne' (add_left_cancel huv)
    have hparam := hEinj z hz heq
    exact sub_left_injective ((div_left_inj' hh.ne').mp hparam)
  have hDreg (z : ℝ × ℝ) (hz : z ∈ K) (u : ℝ) :
      fderiv ℝ (fun v : ℝ => D (z, v)) u 1 ≠ 0 := by
    have hEslice : ContDiff ℝ ∞ (fun v : ℝ => E (z, v)) :=
      hE.comp (contDiff_const.prodMk contDiff_id)
    have hdE := (hEslice.differentiable (by simp)).differentiableAt.hasDerivAt
      (x := (u - a) / h)
    have hdparam : HasDerivAt (fun v : ℝ => (v - a) / h) (1 / h) u :=
      ((hasDerivAt_id u).sub_const a).div_const h
    have hdD := ((hdE.scomp u hdparam).const_smul h).const_add ((a, 0) : ℝ × ℝ)
    have hactual : deriv (fun v : ℝ => D (z, v)) u =
        deriv (fun v : ℝ => E (z, v)) ((u - a) / h) := by
      simpa only [Function.comp_apply, Pi.smul_apply, one_div, smul_smul,
        mul_inv_cancel₀ hh.ne', one_smul] using hdD.deriv
    rw [fderiv_apply_one_eq_deriv, hactual]
    exact hEreg z hz ((u - a) / h)
  let B : ℝ := |a| + h * (n + 6 : ℕ)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hDtail (z : ℝ × ℝ) (u : ℝ) (hu : B ≤ |u|) : D (z, u) = (u, 0) := by
    have hparam : (n + 6 : ℕ) ≤ |(u - a) / h| := by
      rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
      have htriangle : |u| ≤ |u - a| + |a| := by
        simpa only [sub_add_cancel] using abs_add_le (u - a) a
      dsimp only [B] at hu
      nlinarith
    change (a, 0) + h • roundedOpenArcParameter ρ (p z) ((u - a) / h) = _
    rw [hEtail z _ hparam]
    ext <;> dsimp <;> field_simp <;> ring
  have hstandard (t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) (s : ℝ) (k : Fin (n + 2)) :
      p (t, s) k = ((k.val : ℝ), 0) := by
    change h⁻¹ • (Φ (s, t) k - (a, 0)) = _
    rw [hmesh s t ht k]
    ext <;> dsimp <;> field_simp <;> ring
  have hDstat (t s u : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) :
      D ((t, s), u) = D ((t, 0), u) := by
    change (a, 0) + h • roundedOpenArcParameter ρ (p (t, s)) ((u - a) / h) =
      (a, 0) + h • roundedOpenArcParameter ρ (p (t, 0)) ((u - a) / h)
    rw [hEid (t, s) (hstandard t ht s), hEid (t, 0) (hstandard t ht 0)]
  have hDaxis (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ) :
      (D ((t, 1), u)).2 = 0 := by
    have hflat (k : Fin (n + 2)) : (p (t, 1) k).2 = 0 := by
      change h⁻¹ * ((Φ (1, t) k).2 - 0) = 0
      rw [haxis t ht k]
      ring
    change ((a, 0) + h • roundedOpenArcParameter ρ (p (t, 1)) ((u - a) / h)).2 = 0
    simp only [Prod.snd_add, Prod.smul_snd,
      hEaxis (t, 1) hflat, smul_zero, add_zero]
  obtain ⟨G, hG, hGi, hQ, htime, hGaxis⟩ :=
    exists_openArc_tube_homotopy_transport D hB hD hDinj hDreg hDtail hDstat hDaxis
  exact ⟨δ, hδ, hδquarter, ρ, hρ, hρtail, hρbound, hρder,
    G, hG, hGi, hQ, htime, hGaxis⟩

end PoincareConjecture.M25.Topology3D
