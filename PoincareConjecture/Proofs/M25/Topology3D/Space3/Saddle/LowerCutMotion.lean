import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerLevelTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceScalarWindow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceCutConjugacy
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_lower_cut_motion
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (lo z : ℝ)
    (hlo : lo < W.level) (hz : W.level < z)
    (hzc : z < ⟪(u : E3), psi (D.point, 0)⟫_ℝ) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    ∃ (e : ℝ)
      (g : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (K : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (C : Set ℝ),
      let V := Ioo (W.level - 3 * e) (z + 3 * e)
      0 < e ∧
      Icc (W.level - 4 * e) (z + 4 * e) ⊆
        Ioo lo (H (psi (D.point, 0))) ∧
      IsCompact C ∧ C ⊆ V ∧
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => (g p.1).symm p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => K p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (K p.1).symm p.2) ∧
      (∀ r : ℝ, StrictMono (g r) ∧ StrictMono (g r).symm) ∧
      (∀ x : ℝ, g 0 x = x) ∧ (∀ y : E3, K 0 y = y) ∧
      (∀ (r : ℝ) (y : E3),
        H (K r y) = g r (H y) ∧ H ((K r).symm y) = (g r).symm (H y)) ∧
      (∀ (r : ℝ) (y : E3),
        (K r y ∈ S ↔ y ∈ S) ∧ ((K r).symm y ∈ S ↔ y ∈ S)) ∧
      (∀ r : ℝ, K r '' S = S ∧ (K r).symm '' S = S) ∧
      (∀ r x : ℝ, x ∉ C → g r x = x ∧ (g r).symm x = x) ∧
      (∀ (r : ℝ) (y : E3), H y ∉ C → K r y = y ∧ (K r).symm y = y) ∧
      (∀ r : ℝ,
        tsupport (fun x : ℝ => g r x - x) ⊆ C ∧
        tsupport (fun x : ℝ => (g r).symm x - x) ⊆ C) ∧
      (∀ r : ℝ,
        tsupport (fun y : E3 => K r y - y) ⊆ H ⁻¹' C ∧
        tsupport (fun y : E3 => (K r).symm y - y) ⊆ H ⁻¹' C) ∧
      (∀ h : ℝ, |h| ≤ e → ∀ r ∈ Icc (0 : ℝ) 1,
        g r (W.level + h) = W.level + h + r * (z - W.level)) ∧
      (∀ h : ℝ, |h| ≤ e →
        g 1 (W.level + h) = z + h ∧ (g 1).symm (z + h) = W.level + h) ∧
      ∀ h : ℝ, |h| ≤ e →
        K 1 '' (S ∩ {y : E3 | H y = W.level + h}) =
          S ∩ {y : E3 | H y = z + h} ∧
        (K 1).symm '' (S ∩ {y : E3 | H y = z + h}) =
          S ∩ {y : E3 | H y = W.level + h} ∧
        K 1 '' (S ∩ {y : E3 | H y ≤ W.level + h}) =
          S ∩ {y : E3 | H y ≤ z + h} ∧
        (K 1).symm '' (S ∩ {y : E3 | H y ≤ z + h}) =
          S ∩ {y : E3 | H y ≤ W.level + h} ∧
        K 1 '' (S ∩ {y : E3 | W.level + h ≤ H y}) =
          S ∩ {y : E3 | z + h ≤ H y} ∧
        (K 1).symm '' (S ∩ {y : E3 | z + h ≤ H y}) =
          S ∩ {y : E3 | W.level + h ≤ H y} := by
  classical
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
  let c := H (psi (D.point, 0))
  let L := heightPlaneCoordinates u
  let m := (W.level + z) / 2
  obtain ⟨-, -, d, Phi, _hd, hJ, hPhi, hPhii, -, -, -, -, hBand, -, -⟩ :=
    exists_saddle_lower_level_transport psi hpsi u D W z hz.le hzc
  have hscalar := reference_scalar_window lo c W.level z m d
    ⟨hlo, W.level_lt_critical⟩ ⟨hlo.trans hz, hzc⟩
    (by simpa only [min_eq_left hz.le, max_eq_right hz.le] using hJ)
  simp only [min_eq_left hz.le, max_eq_right hz.le] at hscalar
  obtain ⟨e, g, C, he, hbuffer, hC, hCV, hg, hgi, _hgiTime, hg0,
    hmono, hgsupport, hgfixed, hgfixedV, _hgfixedJ, _hgV, htrack, haffine⟩ := hscalar
  let V := Ioo (W.level - 3 * e) (z + 3 * e)
  have hVbuffer : V ⊆ Icc (W.level - 4 * e) (z + 4 * e) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hVJ : V ⊆ Ioo (m - d) (m + d) :=
    fun _ hx => (hbuffer (hVbuffer hx)).2
  obtain ⟨K, hK, hKi, hKformula, hKiformula, hHeight, hMem, hMemInv,
    hImage, _hKfixedV, hK0⟩ :=
    reference_cut_conjugacy u S V W.level Phi hPhi hPhii
      (fun z hz x => hBand z (hVJ hz) x) g hg hgi hg0
      (fun r x hx => (hgfixedV r x hx).1)
  change ∀ r y, H (K r y) = g r (H y) at hHeight
  have hLH (y : E3) : (L y).2 = H y := heightPlaneCoordinates_snd u y
  have hHeightInv (r : ℝ) (y : E3) : H ((K r).symm y) = (g r).symm (H y) := by
    have hh := congrArg (g r).symm (hHeight r ((K r).symm y))
    simpa only [(K r).apply_symm_apply, (g r).symm_apply_apply] using hh.symm
  have hFixed (r : ℝ) (y : E3) (hy : H y ∉ C) :
      K r y = y ∧ (K r).symm y = y := by
    have hf : g r (L y).2 = (L y).2 := by
      simpa only [hLH] using (hgfixed r (H y) hy).1
    have hi : (g r).symm (L y).2 = (L y).2 := by
      simpa only [hLH] using (hgfixed r (H y) hy).2
    constructor
    · rw [hKformula]
      change L.symm (Phi (g r (L y).2) ((Phi (L y).2).symm (L y).1), g r (L y).2) = y
      rw [hf, (Phi (L y).2).apply_symm_apply, Prod.eta, L.symm_apply_apply]
    · rw [hKiformula]
      change L.symm (Phi ((g r).symm (L y).2) ((Phi (L y).2).symm (L y).1),
        (g r).symm (L y).2) = y
      rw [hi, (Phi (L y).2).apply_symm_apply, Prod.eta, L.symm_apply_apply]
  have hSupport (r : ℝ) :
      tsupport (fun y : E3 => K r y - y) ⊆ H ⁻¹' C ∧
      tsupport (fun y : E3 => (K r).symm y - y) ⊆ H ⁻¹' C := by
    constructor
    · apply closure_minimal ?_ (hC.isClosed.preimage H.continuous)
      intro y hy
      change H y ∈ C
      by_contra hn
      exact hy (sub_eq_zero.mpr (hFixed r y hn).1)
    · apply closure_minimal ?_ (hC.isClosed.preimage H.continuous)
      intro y hy
      change H y ∈ C
      by_contra hn
      exact hy (sub_eq_zero.mpr (hFixed r y hn).2)
  have hPredicateImage (p q : ℝ → Prop) (hpq : ∀ x : ℝ, p (g 1 x) ↔ q x) :
      K 1 '' (S ∩ {y : E3 | q (H y)}) = S ∩ {y : E3 | p (H y)} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hqx⟩, rfl⟩
      refine ⟨(hMem 1 x).mpr hx, ?_⟩
      change p (H (K 1 x))
      rw [hHeight]
      exact (hpq (H x)).mpr hqx
    · rintro ⟨hy, hpy⟩
      refine ⟨(K 1).symm y, ⟨(hMemInv 1 y).mpr hy, ?_⟩, (K 1).apply_symm_apply y⟩
      apply (hpq (H ((K 1).symm y))).mp
      rwa [← hHeight 1 ((K 1).symm y), (K 1).apply_symm_apply]
  refine ⟨e, g, K, C, he, fun _ hx => (hbuffer hx).1, hC, hCV,
    hg, hgi, hK, hKi, hmono, hg0, hK0,
    fun r y => ⟨hHeight r y, hHeightInv r y⟩,
    fun r y => ⟨hMem r y, hMemInv r y⟩, hImage, hgfixed, hFixed,
    hgsupport, hSupport, htrack, haffine, ?_⟩
  intro h hh
  have ha : g 1 (W.level + h) = z + h := (haffine h hh).1
  have hlevel : K 1 '' (S ∩ {y : E3 | H y = W.level + h}) =
      S ∩ {y : E3 | H y = z + h} := by
    apply hPredicateImage (fun x => x = z + h) (fun x => x = W.level + h)
    intro x
    rw [← ha]
    exact (g 1).injective.eq_iff
  have hlower : K 1 '' (S ∩ {y : E3 | H y ≤ W.level + h}) =
      S ∩ {y : E3 | H y ≤ z + h} := by
    apply hPredicateImage (fun x => x ≤ z + h) (fun x => x ≤ W.level + h)
    intro x
    rw [← ha]
    exact (hmono 1).1.le_iff_le
  have hupper : K 1 '' (S ∩ {y : E3 | W.level + h ≤ H y}) =
      S ∩ {y : E3 | z + h ≤ H y} := by
    apply hPredicateImage (fun x => z + h ≤ x) (fun x => W.level + h ≤ x)
    intro x
    rw [← ha]
    exact (hmono 1).1.le_iff_le
  refine ⟨hlevel, ?_, hlower, ?_, hupper, ?_⟩
  · rw [← hlevel]
    exact (K 1).symm_image_image _
  · rw [← hlower]
    exact (K 1).symm_image_image _
  · rw [← hupper]
    exact (K 1).symm_image_image _

end PoincareConjecture.M25.Topology3D
