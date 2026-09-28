import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem nonnested_reference_lower_label_images
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdLower : ∀ q : ℝ, 0 ≤ q → -(q ^ 2) / 2 ≤ d q)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (u : UnitTwoSphere) :
    let L := heightPlaneCoordinates u
    let W := (J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph.trans
      L.symm.toDiffeomorph
    let F := (nonnestedReferenceDiffeomorph 0 d hd).trans W
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S : Set E3 := range j
    ∀ (K : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (g : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (_hK : ContDiff ℝ ∞ (fun p : ℝ × E3 => K p.1 p.2))
      (_hKzero : ∀ y : E3, K 0 y = y)
      (_hKmem : ∀ (t : ℝ) (y : E3), K t y ∈ S ↔ y ∈ S)
      (_hKheight : ∀ (t : ℝ) (y : E3), H (K t y) = g t (H y))
      (_hgmono : ∀ t : ℝ, StrictMono (g t))
      (_hgzero : ∀ t : ℝ, g t 0 = 0),
      (∀ (eps : ℝ), eps ≠ 0 → ∀ y ∈ S, H y < 0 → ∀ t : ℝ,
        (0 < eps * (F.symm (K t y)) 1 ↔ 0 < eps * (F.symm y) 1)) ∧
      ∀ (t eps z : ℝ), eps ≠ 0 → z < 0 →
        let E : ℝ → Set E3 := fun a =>
          j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) ≤ a}
        let C : ℝ → Set E3 := fun a =>
          j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) = a}
        K t '' E z = E (g t z) ∧
        (K t).symm '' E (g t z) = E z ∧
        K t '' C z = C (g t z) ∧
        (K t).symm '' C (g t z) = C z := by
  dsimp only
  let L := heightPlaneCoordinates u
  let W := (J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph.trans
    L.symm.toDiffeomorph
  let F := (nonnestedReferenceDiffeomorph 0 d hd).trans W
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S : Set E3 := range j
  intro K g hK hKzero hKmem hKheight hgmono hgzero
  have hNativeHeight (x : E3) :
      H (F x) = 1 + x 2 - (x 1) ^ 2 + d ((x 0) ^ 2 + (x 1) ^ 2) := by
    change ⟪(u : E3), F x⟫_ℝ = _
    rw [← heightPlaneCoordinates_snd u (F x)]
    change (L (L.symm
      (J2.symm (nonnestedReferenceDiffeomorph 0 d hd x).1,
        (nonnestedReferenceDiffeomorph 0 d hd x).2))).2 = _
    rw [L.apply_symm_apply, (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1 x]
    simp only [zero_add]
  have hNativeSphere (y : E3) (hy : y ∈ S) : ‖F.symm y‖ = 1 := by
    rcases hy with ⟨q, rfl⟩
    change ‖F.symm (F (q : E3))‖ = 1
    rw [F.symm_apply_apply]
    exact mem_sphere_zero_iff_norm.mp q.property
  have hNativeAxis (x : E3) (hx : ‖x‖ = 1) (hx1 : x 1 = 0) :
      0 ≤ H (F x) := by
    have hsq : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 = 1 := by
      have hn := EuclideanSpace.real_norm_sq_eq x
      rw [hx, one_pow, Fin.sum_univ_three] at hn
      exact hn.symm
    have hcircle : (x 0) ^ 2 + (x 2) ^ 2 = 1 := by
      simpa only [hx1, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hsq
    have hq0 : 0 ≤ (x 0) ^ 2 := sq_nonneg _
    have hq1 : (x 0) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 2)]
    have hd0 := hdLower ((x 0) ^ 2) hq0
    have hprod := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    rw [hNativeHeight, hx1, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, add_zero]
    nlinarith [sq_nonneg (1 + x 2)]
  have hNativeNonzero (y : E3) (hy : y ∈ S) (hh : H y < 0) :
      (F.symm y) 1 ≠ 0 := by
    intro hzero
    have hbad := hNativeAxis (F.symm y) (hNativeSphere y hy) hzero
    rw [F.apply_symm_apply] at hbad
    exact (not_lt_of_ge hbad) hh
  have hPositiveAlong (f : ℝ → ℝ) (hf : Continuous f)
      (hne : ∀ t : ℝ, f t ≠ 0) (t : ℝ) : (0 < f t ↔ 0 < f 0) := by
    constructor
    · intro ht
      by_contra h0
      obtain ⟨r, hr⟩ := intermediate_value_univ 0 t hf ⟨le_of_not_gt h0, ht.le⟩
      exact hne r hr
    · intro h0
      by_contra ht
      obtain ⟨r, hr⟩ := intermediate_value_univ t 0 hf ⟨le_of_not_gt ht, h0.le⟩
      exact hne r hr
  have hLabels : ∀ (eps : ℝ), eps ≠ 0 → ∀ y ∈ S, H y < 0 → ∀ t : ℝ,
      (0 < eps * (F.symm (K t y)) 1 ↔ 0 < eps * (F.symm y) 1) := by
    intro eps heps y hy hhy t
    have hcoord : Continuous (fun x : E3 => x 1) :=
      (show ContDiff ℝ ∞ (fun x : E3 => x 1) from contDiff_piLp_apply 2).continuous
    have htrack : Continuous (fun r : ℝ => K r y) :=
      (hK.comp (contDiff_id.prodMk contDiff_const)).continuous
    have hcont : Continuous (fun r : ℝ => eps * (F.symm (K r y)) 1) :=
      continuous_const.mul (hcoord.comp (F.symm.contDiff.continuous.comp htrack))
    have hnonzero (r : ℝ) : eps * (F.symm (K r y)) 1 ≠ 0 := by
      apply mul_ne_zero heps
      apply hNativeNonzero (K r y) ((hKmem r y).mpr hy)
      rw [hKheight, ← hgzero r]
      exact hgmono r hhy
    simpa only [hKzero y] using
      hPositiveAlong (fun r : ℝ => eps * (F.symm (K r y)) 1) hcont hnonzero t
  refine ⟨hLabels, ?_⟩
  intro t eps z heps hz
  have hNativePredicate (A : ℝ → Prop) :
      j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ A (H (j q))} =
        S ∩ {y : E3 | 0 < eps * (F.symm y) 1 ∧ A (H y)} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q, rfl⟩, ?_, hq.2⟩
      change 0 < eps * (F.symm (F (q : E3))) 1
      rw [F.symm_apply_apply]
      exact hq.1
    · rintro ⟨⟨q, rfl⟩, hsign, hheight⟩
      refine ⟨q, ⟨?_, hheight⟩, rfl⟩
      change 0 < eps * (F.symm (F (q : E3))) 1 at hsign
      simpa only [F.symm_apply_apply] using hsign
  have hImage (A B : ℝ → Prop) (hAB : ∀ x : ℝ, A (g t x) ↔ B x)
      (hBneg : ∀ x : ℝ, B x → x < 0) :
      K t '' (S ∩ {y : E3 | 0 < eps * (F.symm y) 1 ∧ B (H y)}) =
        S ∩ {y : E3 | 0 < eps * (F.symm y) 1 ∧ A (H y)} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hsign, hheight⟩, rfl⟩
      refine ⟨(hKmem t x).mpr hx,
        (hLabels eps heps x hx (hBneg _ hheight) t).mpr hsign, ?_⟩
      rw [hKheight]
      exact (hAB _).mpr hheight
    · rintro ⟨hy, hsign, hheight⟩
      have hx : (K t).symm y ∈ S := by
        apply (hKmem t ((K t).symm y)).mp
        simpa only [(K t).apply_symm_apply] using hy
      have hxh : B (H ((K t).symm y)) := by
        apply (hAB _).mp
        rwa [← hKheight t ((K t).symm y), (K t).apply_symm_apply]
      refine ⟨(K t).symm y, ⟨hx, ?_, hxh⟩, (K t).apply_symm_apply y⟩
      apply (hLabels eps heps ((K t).symm y) hx (hBneg _ hxh) t).mp
      simpa only [(K t).apply_symm_apply] using hsign
  have hSublevel :
      K t '' (j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) ≤ z}) =
        j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) ≤ g t z} := by
    rw [hNativePredicate (fun x => x ≤ z), hNativePredicate (fun x => x ≤ g t z)]
    exact hImage (fun x => x ≤ g t z) (fun x => x ≤ z)
      (fun _ => (hgmono t).le_iff_le) (fun _ hx => hx.trans_lt hz)
  have hLevel :
      K t '' (j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) = z}) =
        j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) = g t z} := by
    rw [hNativePredicate (fun x => x = z), hNativePredicate (fun x => x = g t z)]
    exact hImage (fun x => x = g t z) (fun x => x = z)
      (fun _ => (g t).injective.eq_iff) (fun _ hx => hx.trans_lt hz)
  refine ⟨hSublevel, ?_, hLevel, ?_⟩
  · rw [← hSublevel]
    exact (K t).symm_image_image _
  · rw [← hLevel]
    exact (K t).symm_image_image _

end PoincareConjecture.M25.Topology3D
