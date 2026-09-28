import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem inverse_eqOn_of_eqOn
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {C : Set E2}
    (hF : EqOn F id C) : EqOn F.symm id C := by
  intro x hx
  apply F.injective
  change F (F.symm x) = F x
  rw [F.apply_symm_apply, hF hx]
  rfl

private theorem image_diff_of_fixed
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {C : Set E2}
    (hF : EqOn F id C) (S : Set E2) : F '' (S \ C) = F '' S \ C := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
    refine ⟨mem_image_of_mem F hy, ?_⟩
    intro hx
    have he := inverse_eqOn_of_eqOn F hF hx
    rw [F.symm_apply_apply] at he
    exact hn (he.symm ▸ hx)
  · rintro ⟨⟨y, hy, rfl⟩, hn⟩
    exact ⟨y, ⟨hy, fun hc => hn (hF hc ▸ hc)⟩, rfl⟩




theorem exists_two_parameter_matching_of_exterior_transport_and_anchor
    (A B : Real → Set E2) (C : Set E2) (I : Set Real) {a : Real} (ha : a ∈ I)
    (hstationary : ∀ t ∈ I, A t \ C = A 0 \ C)
    (hcommon : ∀ t ∈ I, A t ∩ C = B t ∩ C)
    (Ψ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΨ : ContDiff Real ∞ (fun z : Real × E2 => Ψ z.1 z.2))
    (hΨi : ContDiff Real ∞ (fun z : Real × E2 => (Ψ z.1).symm z.2))
    (hQ : ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2))
    (hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2))
    (hΨC : ∀ t, EqOn (Ψ t) id C) (hQC : ∀ u, EqOn (Q u) id C)
    (KΨ KQ : Set E2) (hKΨ : IsCompact KΨ) (hKQ : IsCompact KQ)
    (hΨfix : ∀ t x, x ∉ KΨ → Ψ t x = x)
    (hQfix : ∀ u x, x ∉ KQ → Q u x = x)
    (htransport : ∀ t ∈ I, Ψ t '' (B 0 \ C) = B t \ C)
    (hQ0 : ∀ x, Q 0 x = x) (hanchor : Q 1 '' A a = B a) :
    ∃ K : Set E2, K = KΨ ∪ KQ ∧ IsCompact K ∧
      ∃ Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ u t x, Φ u t x = Ψ (a + u * (t - a)) ((Ψ a).symm (Q u x))) ∧
        (∀ t x, Φ 0 t x = x) ∧
        ContDiff Real ∞ (fun z : Real × Real × E2 => Φ z.1 z.2.1 z.2.2) ∧
        ContDiff Real ∞ (fun z : Real × Real × E2 => (Φ z.1 z.2.1).symm z.2.2) ∧
        (∀ u t x, x ∉ K → Φ u t x = x) ∧
        (∀ u t, EqOn (Φ u t) id C) ∧
        ∀ t ∈ I, Φ 1 t '' A t = B t := by
  let Φ (u t : Real) := ((Q u).trans (Ψ a).symm).trans (Ψ (a + u * (t - a)))
  have hΦC (u t : Real) : EqOn (Φ u t) id C := by
    intro x hx
    change Ψ (a + u * (t - a)) ((Ψ a).symm (Q u x)) = x
    simp only [hQC u hx, id_eq, inverse_eqOn_of_eqOn (Ψ a) (hΨC a) hx,
      hΨC (a + u * (t - a)) hx]
  have hparam : ContDiff Real ∞ (fun z : Real × Real × E2 => a + z.1 * (z.2.1 - a)) := by
    fun_prop
  have hQeval : ContDiff Real ∞ (fun z : Real × Real × E2 => Q z.1 z.2.2) :=
    hQ.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  have hΨieval : ContDiff Real ∞
      (fun z : Real × Real × E2 => (Ψ (a + z.1 * (z.2.1 - a))).symm z.2.2) :=
    hΨi.comp (hparam.prodMk (contDiff_snd.comp contDiff_snd))
  refine ⟨KΨ ∪ KQ, rfl, hKΨ.union hKQ, Φ, fun _ _ _ => rfl, ?_, ?_, ?_, ?_, hΦC, ?_⟩
  · intro t x
    change Ψ (a + 0 * (t - a)) ((Ψ a).symm (Q 0 x)) = x
    simp only [zero_mul, add_zero, hQ0, Diffeomorph.apply_symm_apply]
  · exact hΨ.comp (hparam.prodMk ((Ψ a).symm.contDiff.comp hQeval))
  · exact hQi.comp (contDiff_fst.prodMk ((Ψ a).contDiff.comp hΨieval))
  · intro u t x hx
    have hxΨ : x ∉ KΨ := fun hh => hx (Or.inl hh)
    have hxQ : x ∉ KQ := fun hh => hx (Or.inr hh)
    have hinv : (Ψ a).symm x = x := by
      apply (Ψ a).injective
      change Ψ a ((Ψ a).symm x) = Ψ a x
      rw [(Ψ a).apply_symm_apply, hΨfix a x hxΨ]
    change Ψ (a + u * (t - a)) ((Ψ a).symm (Q u x)) = x
    rw [hQfix u x hxQ, hinv, hΨfix _ x hxΨ]
  · intro t ht
    have hanchorDiff : Q 1 '' (A a \ C) = B a \ C := by
      rw [image_diff_of_fixed (Q 1) (hQC 1), hanchor]
    have hinverse : (Ψ a).symm '' (B a \ C) = B 0 \ C := by
      rw [← htransport a ha, ← image_comp]
      simp only [comp_def, Diffeomorph.symm_apply_apply, image_id']
    have hexterior : Φ 1 t '' (A t \ C) = B t \ C := by
      change (Ψ (a + 1 * (t - a)) ∘ (Ψ a).symm ∘ Q 1) '' (A t \ C) = _
      have htime : a + 1 * (t - a) = t := by ring
      rw [htime, image_comp, image_comp, hstationary t ht, ← hstationary a ha,
        hanchorDiff, hinverse, htransport t ht]
    have hinterior : Φ 1 t '' (A t ∩ C) = A t ∩ C :=
      ((hΦC 1 t).mono inter_subset_right).image_eq_self
    calc
      Φ 1 t '' A t = Φ 1 t '' ((A t \ C) ∪ (A t ∩ C)) := by
        rw [sdiff_union_inter]
      _ = (B t \ C) ∪ (A t ∩ C) := by rw [image_union, hexterior, hinterior]
      _ = B t := by rw [hcommon t ht, sdiff_union_inter]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
