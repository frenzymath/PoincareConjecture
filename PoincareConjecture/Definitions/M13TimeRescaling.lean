import PoincareConjecture.Definitions.M11AdaptedAtlas
import Mathlib.Algebra.Order.GroupWithZero.OrderIso

set_option autoImplicit false

namespace PoincareConjecture

noncomputable def parabolicTime (Q a t : ℝ) : ℝ := Q * (t - a)

noncomputable def parabolicTimeInv (Q a s : ℝ) : ℝ := a + s / Q

@[simp]
theorem parabolicTimeInv_parabolicTime (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) :
    parabolicTimeInv Q a (parabolicTime Q a t) = t := by
  simp [parabolicTimeInv, parabolicTime, hQ.ne']

@[simp]
theorem parabolicTime_parabolicTimeInv (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    parabolicTime Q a (parabolicTimeInv Q a s) = s := by
  simpa [parabolicTime, parabolicTimeInv] using mul_div_cancel₀ s hQ.ne'

noncomputable def parabolicTimeOrderIso (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : ℝ ≃o ℝ where
  toFun := parabolicTime Q a
  invFun := parabolicTimeInv Q a
  left_inv := parabolicTimeInv_parabolicTime Q hQ a
  right_inv := parabolicTime_parabolicTimeInv Q hQ a
  map_rel_iff' := by
    intro s t
    change Q * (s - a) ≤ Q * (t - a) ↔ s ≤ t
    exact (mul_le_mul_iff_right₀ hQ).trans (sub_le_sub_iff_right a)

@[simp]
theorem parabolicTimeOrderIso_apply (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) :
    parabolicTimeOrderIso Q hQ a t = parabolicTime Q a t := rfl

@[simp]
theorem parabolicTimeOrderIso_symm_apply (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    (parabolicTimeOrderIso Q hQ a).symm s = parabolicTimeInv Q a s := rfl

theorem parabolicTime_strictMono (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    StrictMono (parabolicTime Q a) :=
  (parabolicTimeOrderIso Q hQ a).strictMono

theorem parabolicTimeInv_strictMono (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    StrictMono (parabolicTimeInv Q a) :=
  (parabolicTimeOrderIso Q hQ a).symm.strictMono

noncomputable def parabolicInterval (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : SpacetimeInterval where
  domain := parabolicTime Q a '' I.domain
  ordConnected := by
    let : I.domain.OrdConnected := I.ordConnected
    exact Set.ordConnected_image (parabolicTimeOrderIso Q hQ a)
  nontrivial := I.nontrivial.image (parabolicTimeOrderIso Q hQ a).injective

@[simp]
theorem parabolicInterval_domain (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) :
    (parabolicInterval Q hQ a I).domain = parabolicTime Q a '' I.domain := rfl

theorem mem_parabolicInterval_iff (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) (s : ℝ) :
    s ∈ (parabolicInterval Q hQ a I).domain ↔ parabolicTimeInv Q a s ∈ I.domain := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa only [parabolicTimeInv_parabolicTime Q hQ a t] using ht
  · intro hs
    exact ⟨parabolicTimeInv Q a s, hs, parabolicTime_parabolicTimeInv Q hQ a s⟩

@[simp]
theorem parabolicTime_mem_parabolicInterval_iff (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) (t : ℝ) :
    parabolicTime Q a t ∈ (parabolicInterval Q hQ a I).domain ↔ t ∈ I.domain := by
  rw [mem_parabolicInterval_iff Q hQ a I, parabolicTimeInv_parabolicTime Q hQ a t]

end PoincareConjecture
