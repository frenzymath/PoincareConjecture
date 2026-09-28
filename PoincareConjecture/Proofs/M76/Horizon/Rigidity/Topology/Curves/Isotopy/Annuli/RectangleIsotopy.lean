import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.BodyIsotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.CutIsotopy

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Rect" => rectangle (4 * (8 : ℝ)) 1
local notation "I" => unitInterval

theorem exists_cut_rectangle_joint_PL_isotopy
    (e : Rect ≃ₜ Rect) (he : e.IsFinitePL)
    (hfix : ∀ x : Rect, (x : P2) ∈ frontier Rect → e x = x) :
    ∃ (H : I → Rect ≃ₜ Rect) (F Fi : (ℝ × P2) → P2),
      H 0 = Homeomorph.refl Rect ∧ H 1 = e ∧
      (∀ t : I, ∀ x : Rect, (x : P2) ∈ frontier Rect → H t x = x) ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Rect) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Rect) ∧
      (∀ t : I, ∀ x : Rect, F (t, x) = (H t x : P2)) ∧
      (∀ t : I, ∀ x : Rect, Fi (t, x) = ((H t).symm x : P2)) := by
  classical
  let a : P2 ≃ᴬ[ℝ] P2 := ContinuousAffineEquiv.constVAdd ℝ P2 (-16, 0)
  let C : Set P2 := a '' Rect
  let A : Rect ≃ₜ C := a.toHomeomorph.image Rect
  let ec : C ≃ₜ C := A.symm.trans (e.trans A)
  have hec : ec.IsFinitePL := he.affine_conjugate a a
  have hfront : a '' frontier Rect = frontier C := a.toHomeomorph.image_frontier Rect
  have hfixc (x : C) (hx : (x : P2) ∈ frontier C) : ec x = x := by
    obtain ⟨y, hy, hay⟩ := hfront.symm ▸ hx
    have hAx : (A.symm x : P2) = y := by
      change a.symm x = y
      rw [← hay, a.symm_apply_apply]
    change A (e (A.symm x)) = x
    rw [hfix (A.symm x) (hAx.symm ▸ hy), A.apply_symm_apply]
  have hCeq : C = Icc (-16 : ℝ) 16 ×ˢ Icc (-1 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ( -16 + y.1 ∈ Icc (-16 : ℝ) 16) ∧ 0 + y.2 ∈ Icc (-1 : ℝ) 1
      refine ⟨?_, by simpa using hy.2⟩
      constructor <;> linarith [hy.1.1, hy.1.2]
    · intro hx
      refine ⟨(x.1 + 16, x.2), ⟨?_, hx.2⟩, ?_⟩
      · constructor <;> linarith [hx.1.1, hx.1.2]
      · change (-16 + (x.1 + 16), 0 + x.2) = x
        apply Prod.ext <;> ring
  let L : Fin 4 → P2 →ₗ[ℝ] ℝ :=
    ![(1 / 16 : ℝ) • LinearMap.fst ℝ ℝ ℝ,
      (-1 / 16 : ℝ) • LinearMap.fst ℝ ℝ ℝ,
      LinearMap.snd ℝ ℝ ℝ, -LinearMap.snd ℝ ℝ ℝ]
  have hL : ∀ i, L i ≠ 0 := by
    intro i hz
    have h := congrArg (fun f : P2 →ₗ[ℝ] ℝ => f (1, 1)) hz
    fin_cases i <;> norm_num [L] at h
  have hrep : C = {x | ∀ i, L i x ≤ 1} := by
    rw [hCeq]
    ext x
    simp only [mem_prod, mem_Icc, mem_ofPred_eq, Fin.forall_fin_succ,
      L, Matrix.cons_val_zero, Matrix.cons_val_succ,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.neg_apply, Fin.forall_fin_zero, and_true]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      constructor
      · linarith
      · exact ⟨by linarith, h3, by linarith⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, h2⟩
  obtain ⟨Hc, Fc, Fic, hzero, hone, hfixed, hFc, hFic, hv, hiv⟩ :=
    hec.exists_unit_halfspace_body_joint_PL_isotopy hfixc L hL hrep
  let H : I → Rect ≃ₜ Rect := fun t => A.trans ((Hc t).trans A.symm)
  let j : (ℝ × P2) ≃ᴬ[ℝ] (ℝ × P2) :=
    (ContinuousAffineEquiv.refl ℝ ℝ).prodCongr a
  have hjdom : j.symm '' (Icc (0 : ℝ) 1 ×ˢ C) = Icc (0 : ℝ) 1 ×ˢ Rect := by
    ext p
    constructor
    · rintro ⟨q, ⟨ht, ⟨x, hx, hax⟩⟩, rfl⟩
      refine ⟨ht, ?_⟩
      change a.symm q.2 ∈ Rect
      rw [← hax, a.symm_apply_apply]
      exact hx
    · intro hp
      exact ⟨j p, ⟨hp.1, ⟨p.2, hp.2, rfl⟩⟩, j.symm_apply_apply p⟩
  have hFP := (hFc.precomp_affineEquiv j).postcomp a.symm.toContinuousAffineMap
  have hFiP := (hFic.precomp_affineEquiv j).postcomp a.symm.toContinuousAffineMap
  rw [hjdom] at hFP hFiP
  refine ⟨H, a.symm ∘ (Fc ∘ j), a.symm ∘ (Fic ∘ j), ?_, ?_, ?_,
    hFP, hFiP, ?_, ?_⟩
  · apply Homeomorph.ext
    intro x
    apply Subtype.ext
    change (A.symm (Hc 0 (A x)) : P2) = x
    rw [hzero]
    simp
  · apply Homeomorph.ext
    intro x
    apply Subtype.ext
    change (A.symm (Hc 1 (A x)) : P2) = e x
    rw [hone]
    simp [ec]
  · intro t x hx
    change A.symm (Hc t (A x)) = x
    rw [hfixed t (A x) (hfront ▸ mem_image_of_mem a hx), A.symm_apply_apply]
  · intro t x
    change a.symm (Fc ((t : ℝ), a x)) = a.symm (Hc t (A x))
    exact congrArg a.symm (hv t (A x))
  · intro t x
    change a.symm (Fic ((t : ℝ), a x)) = a.symm ((Hc t).symm (A x))
    exact congrArg a.symm (hiv t (A x))

theorem exists_joint_PL_annulus_isotopy_of_cut_rectangle
    (e : Rect ≃ₜ Rect) (he : e.IsFinitePL)
    (hfix : ∀ x : Rect, (x : P2) ∈ frontier Rect → e x = x) :
    ∃ (A : I → squareAnnulus 8 1 ≃ₜ squareAnnulus 8 1)
      (g gi : (ℝ × P2) → P2),
      A 0 = Homeomorph.refl (squareAnnulus 8 1) ∧
      FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ squareAnnulus 8 1) ∧
      FinitePiecewiseAffineOn gi (Icc (0 : ℝ) 1 ×ˢ squareAnnulus 8 1) ∧
      (∀ t : I, ∀ x : squareAnnulus 8 1, g (t, x) = (A t x : P2)) ∧
      (∀ t : I, ∀ x : squareAnnulus 8 1, gi (t, x) = ((A t).symm x : P2)) ∧
      Continuous (fun p : I × squareAnnulus 8 1 => A p.1 p.2) ∧
      Continuous (fun p : I × squareAnnulus 8 1 => (A p.1).symm p.2) ∧
      (∀ (t : I) (side : Bool) z, A t (annulusRimPoint side z) = annulusRimPoint side z) ∧
      ∀ (s : ℝ) (hs : s ∈ Icc 0 (4 * (8 : ℝ))) (u : Icc (-1 : ℝ) 1),
        (A 1 ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * (8 : ℝ))), u),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : P2) =
        annulusMap 8 (by norm_num)
          (((e ⟨(s, u), hs, u.property⟩ : P2).1 : AddCircle (4 * (8 : ℝ))),
            (e ⟨(s, u), hs, u.property⟩ : P2).2) := by
  obtain ⟨H, F, Fi, hzero, hone, hfixed, hF, hFi, hv, hiv⟩ :=
    exists_cut_rectangle_joint_PL_isotopy e he hfix
  have hfaces (x : Rect)
      (hx : (x : P2).1 = 0 ∨ (x : P2).1 = 4 * (8 : ℝ) ∨
        (x : P2).2 = -1 ∨ (x : P2).2 = 1) : (x : P2) ∈ frontier Rect := by
    change (x : P2) ∈ frontier (Icc (0 : ℝ) (4 * 8) ×ˢ Icc (-1 : ℝ) 1)
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
      frontier_Icc (by norm_num : (0 : ℝ) ≤ 4 * 8),
      frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    have hp := x.property
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    rcases hx with h | h | h | h
    · exact Or.inr ⟨Or.inl h, hp.2⟩
    · exact Or.inr ⟨Or.inr h, hp.2⟩
    · exact Or.inl ⟨hp.1, Or.inl h⟩
    · exact Or.inl ⟨hp.1, Or.inr h⟩
  obtain ⟨A, g, gi, hg, hgi, hgv, hgiv, hc, hci, hrims, hperiod⟩ :=
    exists_joint_PL_annulus_family_of_cut_rectangle H F Fi hF hFi hv hiv
      (fun t x hx => hfixed t x (hfaces x hx))
  refine ⟨A, g, gi, ?_, hg, hgi, hgv, hgiv, hc, hci, hrims, ?_⟩
  · apply Homeomorph.ext
    intro x
    obtain ⟨s, hs, hxs⟩ := exists_period_parameter_of_depth
      (L := 8) (d := 1) (by norm_num) (by norm_num) x
    let u : Icc (-1 : ℝ) 1 := ⟨depth 8 x, mem_squareAnnulus_iff_depth.mp x.property⟩
    have h := hperiod 0 s hs u
    rw [hzero] at h
    apply Subtype.ext
    have hx : (⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * (8 : ℝ))), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ :
        squareAnnulus 8 1) = x := Subtype.ext hxs.symm
    rw [hx] at h
    exact h.trans hxs.symm
  · intro s hs u
    simpa only [hone] using hperiod 1 s hs u

end PoincareConjecture.M76.Dehn
