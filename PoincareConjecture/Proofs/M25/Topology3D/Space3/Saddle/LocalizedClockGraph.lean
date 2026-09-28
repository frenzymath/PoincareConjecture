import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart

set_option autoImplicit false

open Set
open scoped ContDiff NNReal Manifold

namespace PoincareConjecture.M25.Topology3D

variable (V : ℝ × E2 → E2) {K L : ℝ≥0}
variable (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)
variable (hV : ContDiff ℝ ∞ V) (hsV : HasCompactSupport V)
variable (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (c : ℝ)

noncomputable def localizedClockGraphDiffeomorph (s : ℝ) :
    Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ := by
  let a (z : ℝ) := c + s * χ z * (z - c)
  have ha : ContDiff ℝ ∞ a :=
    contDiff_const.add ((contDiff_const.mul hχ).mul (contDiff_id.sub contDiff_const))
  let Φ (z : ℝ) := clockEvolutionDiffeomorph V hK hL hV hsV c (a z)
  have hΦ : ContDiff ℝ ∞ (fun p : ℝ × E2 => Φ p.1 p.2) :=
    (clockEvolution_contDiff V hK hL hV hsV).comp
      ((contDiff_const.prodMk (ha.comp contDiff_fst)).prodMk contDiff_snd)
  have hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Φ p.1).symm p.2) :=
    (clockEvolution_contDiff V hK hL hV hsV).comp
      (((ha.comp contDiff_fst).prodMk contDiff_const).prodMk contDiff_snd)
  exact planarFamilyGraphDiffeomorph Φ hΦ hi

local notation "G" => localizedClockGraphDiffeomorph V hK hL hV hsV χ hχ c
local notation "Xi" => clockEvolution V hK hL

theorem localizedClockGraphDiffeomorph_apply (s : ℝ) (p : E2 × ℝ) :
    G s p = (Xi c (c + s * χ p.2 * (p.2 - c)) p.1, p.2) := rfl

theorem localizedClockGraphDiffeomorph_symm_apply (s : ℝ) (p : E2 × ℝ) :
    (G s).symm p = (Xi (c + s * χ p.2 * (p.2 - c)) c p.1, p.2) := rfl

theorem localizedClockGraphDiffeomorph_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => (G p.1).symm p.2) := by
  have ha : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) =>
      c + p.1 * χ p.2.2 * (p.2.2 - c)) :=
    contDiff_const.add ((contDiff_fst.mul (hχ.comp contDiff_snd.snd)).mul
      (contDiff_snd.snd.sub contDiff_const))
  exact ⟨((clockEvolution_contDiff V hK hL hV hsV).comp
    ((contDiff_const.prodMk ha).prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd,
    ((clockEvolution_contDiff V hK hL hV hsV).comp
      ((ha.prodMk contDiff_const).prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd⟩

theorem localizedClockGraphDiffeomorph_zero (p : E2 × ℝ) : G 0 p = p := by
  simp only [localizedClockGraphDiffeomorph_apply, zero_mul, add_zero,
    clockEvolution_self, Prod.eta]

theorem localizedClockGraphDiffeomorph_height (s : ℝ) (p : E2 × ℝ) :
    (G s p).2 = p.2 ∧ ((G s).symm p).2 = p.2 := ⟨rfl, rfl⟩

theorem localizedClockGraphDiffeomorph_fixed_cylinder
    {B : Set E2} (hzero : ∀ z : ℝ, ∀ x ∈ B, V (z, x) = 0)
    (s z : ℝ) (x : E2) (hx : x ∈ B) :
    G s (x, z) = (x, z) ∧ (G s).symm (x, z) = (x, z) := by
  constructor
  · apply Prod.ext
    · exact clockEvolution_eq_self V hK hL x (fun t => hzero t x hx) _ _
    · rfl
  · apply Prod.ext
    · exact clockEvolution_eq_self V hK hL x (fun t => hzero t x hx) _ _
    · rfl

theorem localizedClockGraphDiffeomorph_fixed_of_cutoff_zero
    (s z : ℝ) (x : E2) (hz : χ z = 0) :
    G s (x, z) = (x, z) ∧ (G s).symm (x, z) = (x, z) := by
  constructor <;> simp only [localizedClockGraphDiffeomorph_apply,
    localizedClockGraphDiffeomorph_symm_apply, hz, mul_zero, zero_mul,
    add_zero, clockEvolution_self]

theorem localizedClockGraphDiffeomorph_tsupport_subset (s : ℝ) :
    tsupport (fun p => G s p - p) ⊆ (Prod.snd '' tsupport V) ×ˢ tsupport χ ∧
      tsupport (fun p => (G s).symm p - p) ⊆
        (Prod.snd '' tsupport V) ×ˢ tsupport χ := by
  have hclosed : IsClosed ((Prod.snd '' tsupport V) ×ˢ tsupport χ) :=
    (hsV.isCompact.image continuous_snd).isClosed.prod (isClosed_tsupport χ)
  constructor
  · apply closure_minimal ?_ hclosed
    intro p hp
    constructor
    · apply clockEvolution_support_subset V hK hL c (c + s * χ p.2 * (p.2 - c))
      intro hz
      apply hp
      apply sub_eq_zero.mpr
      exact Prod.ext (sub_eq_zero.mp hz) rfl
    · by_contra hz
      exact hp (sub_eq_zero.mpr
        (localizedClockGraphDiffeomorph_fixed_of_cutoff_zero V hK hL hV hsV χ hχ c
          s p.2 p.1 (image_eq_zero_of_notMem_tsupport hz)).1)
  · apply closure_minimal ?_ hclosed
    intro p hp
    constructor
    · apply clockEvolution_support_subset V hK hL (c + s * χ p.2 * (p.2 - c)) c
      intro hz
      apply hp
      apply sub_eq_zero.mpr
      exact Prod.ext (sub_eq_zero.mp hz) rfl
    · by_contra hz
      exact hp (sub_eq_zero.mpr
        (localizedClockGraphDiffeomorph_fixed_of_cutoff_zero V hK hL hV hsV χ hχ c
          s p.2 p.1 (image_eq_zero_of_notMem_tsupport hz)).2)

theorem localizedClockGraphDiffeomorph_hasCompactSupport
    (hsχ : HasCompactSupport χ) (s : ℝ) :
    HasCompactSupport (fun p => G s p - p) ∧
      HasCompactSupport (fun p => (G s).symm p - p) := by
  have hcompact : IsCompact ((Prod.snd '' tsupport V) ×ˢ tsupport χ) :=
    (hsV.isCompact.image continuous_snd).prod hsχ.isCompact
  have hs := localizedClockGraphDiffeomorph_tsupport_subset V hK hL hV hsV χ hχ c s
  exact ⟨hcompact.of_isClosed_subset (isClosed_tsupport _) hs.1,
    hcompact.of_isClosed_subset (isClosed_tsupport _) hs.2⟩

theorem localizedClockGraphDiffeomorph_mem_symm_image
    (S0 : Set (E2 × ℝ)) (s : ℝ) (p : E2 × ℝ) :
    p ∈ (G s).symm '' S0 ↔ G s p ∈ S0 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [Diffeomorph.apply_symm_apply] using hq
  · intro hp
    exact ⟨G s p, hp, (G s).symm_apply_apply p⟩

end PoincareConjecture.M25.Topology3D
