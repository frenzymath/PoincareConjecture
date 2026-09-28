import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace Poincare.Manifold.Schoenflies.Plane



theorem exists_time_preserving_diffeomorph_fibers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × E) ≃ₘ[ℝ] (ℝ × E)) (htime : ∀ p, (D p).1 = p.1)
    (hcompact : HasCompactSupport (fun p => D p - p)) :
    ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      (∀ z x, F z x = (D (z, x)).2) ∧
      (∀ z x, (F z).symm x = (D.symm (z, x)).2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      (∃ K : Set E, IsCompact K ∧
        ∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
      ∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x) := by
  let f : ℝ → E → E := fun z x => (D (z, x)).2
  let g : ℝ → E → E := fun z x => (D.symm (z, x)).2
  have hInvtime (p : ℝ × E) : (D.symm p).1 = p.1 := by
    simpa only [D.apply_symm_apply] using (htime (D.symm p)).symm
  have hD (z : ℝ) (x : E) : D (z, x) = (z, f z x) :=
    Prod.ext (htime (z, x)) rfl
  have hG (z : ℝ) (x : E) : D.symm (z, x) = (z, g z x) :=
    Prod.ext (hInvtime (z, x)) rfl
  have hleft (z : ℝ) : LeftInverse (g z) (f z) := by
    intro x
    have h := congrArg Prod.snd (D.symm_apply_apply (z, x))
    rw [hD] at h
    exact h
  have hright (z : ℝ) : LeftInverse (f z) (g z) := by
    intro x
    have h := congrArg Prod.snd (D.apply_symm_apply (z, x))
    rw [hG] at h
    exact h
  let F : ℝ → (E ≃ₘ[ℝ] E) := fun z =>
    { toEquiv :=
        { toFun := f z
          invFun := g z
          left_inv := hleft z
          right_inv := hright z }
      contMDiff_toFun := (D.contDiff.comp (contDiff_const.prodMk contDiff_id)).snd.contMDiff
      contMDiff_invFun :=
        (D.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)).snd.contMDiff }
  obtain ⟨C, hC, hCzero⟩ := exists_compact_iff_hasCompactSupport.mpr hcompact
  let K : Set E := Prod.snd '' C
  have hK : IsCompact K := hC.image continuous_snd
  have hfixed (z : ℝ) (x : E) (hx : x ∉ K) : F z x = x ∧ (F z).symm x = x := by
    have hp : (z, x) ∉ C := fun h => hx ⟨(z, x), h, rfl⟩
    have hDx : D (z, x) = (z, x) := sub_eq_zero.mp (hCzero (z, x) hp)
    have hf : F z x = x := congrArg Prod.snd hDx
    refine ⟨hf, ?_⟩
    have h := congrArg (F z).symm hf
    simpa only [(F z).symm_apply_apply] using h.symm
  refine ⟨F, (fun _ _ => rfl), (fun _ _ => rfl), D.contDiff.snd,
    D.symm.contDiff.snd, ⟨K, hK, hfixed⟩, ?_⟩
  intro z
  exact ⟨HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfixed z x hx).1),
    HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfixed z x hx).2)⟩

end Poincare.Manifold.Schoenflies.Plane
