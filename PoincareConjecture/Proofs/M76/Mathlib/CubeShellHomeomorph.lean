import PoincareConjecture.Proofs.M76.Mathlib.CubeShellMap
import PoincareConjecture.Proofs.M76.Mathlib.SquareShellIdentity

set_option autoImplicit false

open Set Geometry

namespace CubeShell

private theorem radiusMap_inverse {a b c d : ℝ} (hab : a < b) (hcd : c < d) (r : ℝ) :
    SquareShell.radiusMap c d a b (SquareShell.radiusMap a b c d r) = r := by
  unfold SquareShell.radiusMap
  field_simp [(sub_pos.mpr hab).ne', (sub_pos.mpr hcd).ne']
  ring

private theorem abs_eq_radius_iff {u r : ℝ} (hr : 0 ≤ r) :
    |u| = r ↔ u = -r ∨ u = r := by
  constructor
  · intro h
    rcases le_total 0 u with hu | hu
    · exact Or.inr ((abs_of_nonneg hu).symm.trans h)
    · left
      have hn := (abs_of_nonpos hu).symm.trans h
      linarith
  · rintro (rfl | rfl) <;> simp only [abs_neg, abs_of_nonneg hr]

theorem exists_radius_homeomorph {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    ∃ H : shell a b ≃ₜ shell c d, H.IsFinitePL ∧
      ∀ x : shell a b,
        ‖(H x : Ambient)‖ = SquareShell.radiusMap a b c d ‖(x : Ambient)‖ ∧
        (‖(x : Ambient)‖ = a → (H x : Ambient) = (c / a) • (x : Ambient)) ∧
        (‖(x : Ambient)‖ = b → (H x : Ambient) = (d / b) • (x : Ambient)) := by
  obtain ⟨e, he, hdata⟩ := SquareShell.exists_sector_radius_homeomorph ha hab hc hcd
  obtain ⟨g, hg, heg⟩ := he.symm
  obtain ⟨f, hf, hef⟩ := he
  have hmapf : MapsTo f (SquareShell.sector a b) (SquareShell.sector c d) := by
    intro p hp
    rw [← hef ⟨p, hp⟩]
    exact (e ⟨p, hp⟩).property
  have hmapg : MapsTo g (SquareShell.sector c d) (SquareShell.sector a b) := by
    intro p hp
    rw [← heg ⟨p, hp⟩]
    exact (e.symm ⟨p, hp⟩).property
  have hradf (p : ℝ × ℝ) (hp : p ∈ SquareShell.sector a b) :
      (f p).2 = SquareShell.radiusMap a b c d p.2 := by
    rw [← hef ⟨p, hp⟩]
    exact (hdata _).1
  have hradg (p : ℝ × ℝ) (hp : p ∈ SquareShell.sector c d) :
      (g p).2 = SquareShell.radiusMap c d a b p.2 := by
    have h := (hdata (e.symm ⟨p, hp⟩)).1
    rw [e.apply_symm_apply] at h
    rw [← heg ⟨p, hp⟩, h, radiusMap_inverse hab hcd]
  have hedge (p : SquareShell.sector a b) :
      |(p : ℝ × ℝ).1| = (p : ℝ × ℝ).2 ↔
        |(e p : ℝ × ℝ).1| = (e p : ℝ × ℝ).2 := by
    rw [abs_eq_radius_iff (ha.le.trans p.property.1.1),
      abs_eq_radius_iff (hc.le.trans (e p).property.1.1)]
    exact or_congr (hdata p).2.1 (hdata p).2.2.1
  have hedgef (p : ℝ × ℝ) (hp : p ∈ SquareShell.sector a b)
      (hed : |p.1| = p.2) : |(f p).1| = (f p).2 := by
    rw [← hef ⟨p, hp⟩]
    exact (hedge ⟨p, hp⟩).mp hed
  have hedgeg (p : ℝ × ℝ) (hp : p ∈ SquareShell.sector c d)
      (hed : |p.1| = p.2) : |(g p).1| = (g p).2 := by
    rw [← heg ⟨p, hp⟩]
    apply (hedge (e.symm ⟨p, hp⟩)).mpr
    simpa only [e.apply_symm_apply] using hed
  have hleft : LeftInvOn g f (SquareShell.sector a b) := by
    intro p hp
    rw [← hef ⟨p, hp⟩, ← heg, e.symm_apply_apply]
  have hright : LeftInvOn f g (SquareShell.sector c d) := by
    intro p hp
    rw [← heg ⟨p, hp⟩, ← hef, e.apply_symm_apply]
  have hFmap : MapsTo (lift f) (shell a b) (shell c d) :=
    fun _ hx => lift_mem_shell hmapf hradf hedgef hx
  have hGmap : MapsTo (lift g) (shell c d) (shell a b) :=
    fun _ hx => lift_mem_shell hmapg hradg hedgeg hx
  have hGF := lift_leftInvOn hmapf hradf hedgef hleft
  have hFG := lift_leftInvOn hmapg hradg hedgeg hright
  obtain ⟨K, hK, hKs⟩ := exists_finite_shell_complex a (ha.trans hab)
  have hFPL : FinitePiecewiseAffineOn (lift f) (shell a b) := by
    rw [← hKs]
    exact finitePiecewiseAffineOn_lift hf K hK hKs.subset
  have hFimage : lift f '' shell a b = shell c d :=
    Subset.antisymm (image_subset_iff.mpr hFmap)
      (fun y hy => ⟨lift g y, hGmap hy, hFG hy⟩)
  obtain ⟨H, hH, hHval⟩ := hFPL.exists_homeomorph_image hGF.injOn
  let G := H.trans (Homeomorph.setCongr hFimage)
  have hGPL : G.IsFinitePL := ⟨lift f, hFPL, hHval⟩
  refine ⟨G, hGPL, ?_⟩
  intro x
  have hGval : (G x : Ambient) = lift f x := hHval x
  refine ⟨hGval ▸ norm_lift hmapf hradf hedgef x.property, ?_, ?_⟩
  · intro hx
    have hcoords (i : Fin 3) :
        (f (coordinatePair i x)).1 = (c / a) * coordinate i x := by
      let p : SquareShell.sector a b := ⟨coordinatePair i x,
        coordinatePair_mem_sector x.property i⟩
      have h := (hdata p).2.2.2.1 hx
      rw [hef] at h
      exact congrArg Prod.fst h
    rw [hGval]
    change ((_, _), _) = ((_, _), _)
    exact Prod.ext (Prod.ext (hcoords 0) (hcoords 1)) (hcoords 2)
  · intro hx
    have hcoords (i : Fin 3) :
        (f (coordinatePair i x)).1 = (d / b) * coordinate i x := by
      let p : SquareShell.sector a b := ⟨coordinatePair i x,
        coordinatePair_mem_sector x.property i⟩
      have h := (hdata p).2.2.2.2 hx
      rw [hef] at h
      exact congrArg Prod.fst h
    rw [hGval]
    change ((_, _), _) = ((_, _), _)
    exact Prod.ext (Prod.ext (hcoords 0) (hcoords 1)) (hcoords 2)

theorem exists_fixed_radius_homeomorph {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    ∃ H : shell a b ≃ₜ shell c d, H.IsFinitePL ∧
      (∀ x : shell a b,
        ‖(H x : Ambient)‖ = SquareShell.radiusMap a b c d ‖(x : Ambient)‖ ∧
        (‖(x : Ambient)‖ = a → (H x : Ambient) = (c / a) • (x : Ambient)) ∧
        (‖(x : Ambient)‖ = b → (H x : Ambient) = (d / b) • (x : Ambient))) ∧
      (a = c → b = d → ∀ x : shell a b, (H x : Ambient) = x) := by
  by_cases hsame : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := hsame
    obtain ⟨K, hK, hKs⟩ := exists_finite_shell_complex a (ha.trans hab)
    have href : (Homeomorph.refl (shell a b)).IsFinitePL :=
      ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ Ambient)⟩,
        fun _ => rfl⟩
    refine ⟨Homeomorph.refl _, href, ?_, fun _ _ _ => rfl⟩
    intro x
    change ‖(x : Ambient)‖ = SquareShell.radiusMap a b a b ‖(x : Ambient)‖ ∧ _
    rw [SquareShell.radiusMap_self hab]
    exact ⟨rfl, fun _ => by simp [div_self ha.ne'],
      fun _ => by simp [div_self (ha.trans hab).ne']⟩
  · obtain ⟨H, hH, hdata⟩ := exists_radius_homeomorph ha hab hc hcd
    exact ⟨H, hH, hdata, fun h₁ h₂ => False.elim (hsame ⟨h₁, h₂⟩)⟩

end CubeShell
