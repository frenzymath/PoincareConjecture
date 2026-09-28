import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Relative.Localization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_supported_agreement_of_fixed_halfspace_preserving_linear
    (l : E →L[Real] Real) (v : E) (hlv : l v = 1) (c : Real)
    (F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hF : EqOn F id {x | c ≤ l x}) {K : Set E} (hK : IsCompact K)
    (m : E →L[Real] Real) (hlinear : ∀ x, m (F x) = m x) :
    ∃ S : Set E, IsCompact S ∧
      ∃ G : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x ∉ S, G x = x) ∧ EqOn G id {x | c ≤ l x} ∧
        (∀ x, m (G x) = m x) ∧ EqOn G F K := by
  obtain ⟨a, ha⟩ := (hK.image l.continuous).bddBelow
  let σ : Real → Real := fun t => max 0 (c - a) * (t - 1) ^ 2
  have hσ : ContDiff Real ∞ σ := contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 2)
  have hσpos (t : Real) : 0 ≤ σ t := mul_nonneg (le_max_left _ _) (sq_nonneg _)
  let T (t : Real) : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toEquiv := Equiv.addRight (σ t • v)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let Φ (t : Real) := ((T t).trans F).trans (T t).symm
  have hΦ (t : Real) (x : E) : Φ t x = F (x + σ t • v) - σ t • v := by
    change F (x + σ t • v) + -(σ t • v) = _
    rw [sub_eq_add_neg]
  have hΦsmooth : ContDiff Real ∞ (fun z : Real × E => Φ z.1 z.2) := by
    change ContDiff Real ∞ (fun z : Real × E => F (z.2 + σ z.1 • v) + -(σ z.1 • v))
    exact (F.contMDiff.contDiff.comp (contDiff_snd.add
      ((hσ.comp contDiff_fst).smul contDiff_const))).add
        (((hσ.comp contDiff_fst).smul contDiff_const).neg)
  have hΦinverse : ContDiff Real ∞ (fun z : Real × E => (Φ z.1).symm z.2) := by
    change ContDiff Real ∞ (fun z : Real × E => F.symm (z.2 + σ z.1 • v) + -(σ z.1 • v))
    exact (F.symm.contMDiff.contDiff.comp (contDiff_snd.add
      ((hσ.comp contDiff_fst).smul contDiff_const))).add
        (((hσ.comp contDiff_fst).smul contDiff_const).neg)
  have hzero (x : E) (hx : x ∈ K) : Φ 0 x = x := by
    have hml : a ≤ l x := ha (mem_image_of_mem l hx)
    have hshift : c ≤ l (x + σ 0 • v) := by
      rw [map_add, map_smul, hlv]
      simp only [σ, zero_sub, neg_one_sq, mul_one, smul_eq_mul]
      linarith [le_max_right (0 : Real) (c - a)]
    rw [hΦ, hF hshift, id_eq, add_sub_cancel_right]
  have hstationary (t : Real) (x : E) (hx : x ∈ {x | c ≤ l x}) : Φ t x = x := by
    have hshift : c ≤ l (x + σ t • v) := by
      rw [map_add, map_smul, hlv, smul_eq_mul, mul_one]
      exact hx.trans (le_add_of_nonneg_right (hσpos t))
    rw [hΦ, hF hshift, id_eq, add_sub_cancel_right]
  have hlevel (t : Real) (x : E) : m (Φ t x) = m x := by
    rw [hΦ, map_sub, hlinear, map_add, add_sub_cancel_right]
  obtain ⟨S, hS, _, G, hfix, hfixed, hlevelG, hagree⟩ :=
    exists_supported_relative_family_localization_preserving_linear
      Φ hΦsmooth hΦinverse hK
      isOpen_univ (fun _ _ _ _ => mem_univ _) hzero hstationary m hlevel
  refine ⟨S, hS, G, hfix, hfixed, hlevelG, ?_⟩
  intro x hx
  have hh := hagree hx
  simpa only [hΦ, σ, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_smul, add_zero, sub_zero] using hh

theorem exists_supported_agreement_of_fixed_halfspace
    (l : E →L[Real] Real) (v : E) (hlv : l v = 1) (c : Real)
    (F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hF : EqOn F id {x | c ≤ l x}) {K : Set E} (hK : IsCompact K) :
    ∃ S : Set E, IsCompact S ∧
      ∃ G : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x ∉ S, G x = x) ∧ EqOn G id {x | c ≤ l x} ∧ EqOn G F K := by
  obtain ⟨S, hS, G, hfix, hhalf, _, hagree⟩ :=
    exists_supported_agreement_of_fixed_halfspace_preserving_linear
      l v hlv c F hF hK 0 (by simp)
  exact ⟨S, hS, G, hfix, hhalf, hagree⟩

end Poincare.Manifold.Schoenflies
