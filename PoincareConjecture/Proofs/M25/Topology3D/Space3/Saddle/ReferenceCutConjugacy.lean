import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable (u : UnitTwoSphere)

theorem reference_cut_conjugacy
    (surface : Set E3) (V : Set ℝ) (c0 : ℝ)
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hPhii : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi p.1).symm p.2))
    (hBand : ∀ z ∈ V, ∀ x : E2,
      (heightPlaneCoordinates u).symm (Phi z x, z) ∈ surface ↔
        (heightPlaneCoordinates u).symm (x, c0) ∈ surface)
    (g : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2))
    (hgi : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (g p.1).symm p.2))
    (hg0 : ∀ z : ℝ, g 0 z = z)
    (hgOutside : ∀ t z : ℝ, z ∉ V → g t z = z) :
    let L := heightPlaneCoordinates u
    ∃ K : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E3 => K p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (K p.1).symm p.2) ∧
      (∀ t y, K t y =
        L.symm (Phi (g t (L y).2) ((Phi (L y).2).symm (L y).1),
          g t (L y).2)) ∧
      (∀ t y, (K t).symm y =
        L.symm (Phi ((g t).symm (L y).2) ((Phi (L y).2).symm (L y).1),
          (g t).symm (L y).2)) ∧
      (∀ t y, ⟪(u : E3), K t y⟫_ℝ = g t ⟪(u : E3), y⟫_ℝ) ∧
      (∀ t y, K t y ∈ surface ↔ y ∈ surface) ∧
      (∀ t y, (K t).symm y ∈ surface ↔ y ∈ surface) ∧
      (∀ t, K t '' surface = surface ∧ (K t).symm '' surface = surface) ∧
      (∀ t y, ⟪(u : E3), y⟫_ℝ ∉ V →
        K t y = y ∧ (K t).symm y = y) ∧
      (∀ y, K 0 y = y) := by
  dsimp only
  let L := heightPlaneCoordinates u
  let Q := planarFamilyGraphDiffeomorph Phi hPhi hPhii
  let A : ℝ → Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
      (E2 × ℝ) (E2 × ℝ) ∞ := fun t => {
    toEquiv := (Equiv.refl E2).prodCongr (g t).toEquiv
    contMDiff_toFun :=
      (contDiff_fst.prodMk ((g t).contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun :=
      (contDiff_fst.prodMk ((g t).symm.contDiff.comp contDiff_snd)).contMDiff }
  let K : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ := fun t =>
    L.toDiffeomorph.trans
      (Q.symm.trans ((A t).trans (Q.trans L.symm.toDiffeomorph)))
  have hA : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => A p.1 p.2) := by
    change ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => (p.2.1, g p.1 p.2.2))
    exact contDiff_snd.fst.prodMk
      (hg.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hAi : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => (A p.1).symm p.2) := by
    change ContDiff ℝ ∞
      (fun p : ℝ × (E2 × ℝ) => (p.2.1, (g p.1).symm p.2.2))
    exact contDiff_snd.fst.prodMk
      (hgi.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hRight : ContDiff ℝ ∞ (fun p : ℝ × E3 => Q.symm (L p.2)) :=
    Q.symm.contDiff.comp (L.contDiff.comp contDiff_snd)
  have hKs : ContDiff ℝ ∞ (fun p : ℝ × E3 => K p.1 p.2) := by
    change ContDiff ℝ ∞
      (fun p : ℝ × E3 => L.symm (Q (A p.1 (Q.symm (L p.2)))))
    exact L.symm.contDiff.comp
      (Q.contDiff.comp (hA.comp (contDiff_fst.prodMk hRight)))
  have hKis : ContDiff ℝ ∞ (fun p : ℝ × E3 => (K p.1).symm p.2) := by
    change ContDiff ℝ ∞
      (fun p : ℝ × E3 => L.symm (Q ((A p.1).symm (Q.symm (L p.2)))))
    exact L.symm.contDiff.comp
      (Q.contDiff.comp (hAi.comp (contDiff_fst.prodMk hRight)))
  have hK (t : ℝ) (y : E3) : K t y =
      L.symm (Phi (g t (L y).2) ((Phi (L y).2).symm (L y).1),
        g t (L y).2) := rfl
  have hKi (t : ℝ) (y : E3) : (K t).symm y =
      L.symm (Phi ((g t).symm (L y).2) ((Phi (L y).2).symm (L y).1),
        (g t).symm (L y).2) := rfl
  have hHL (y : E3) : (L y).2 = ⟪(u : E3), y⟫_ℝ :=
    heightPlaneCoordinates_snd u y
  have hHeight (t : ℝ) (y : E3) :
      ⟪(u : E3), K t y⟫_ℝ = g t ⟪(u : E3), y⟫_ℝ := by
    rw [← hHL (K t y), hK, L.apply_symm_apply]
    exact congrArg (g t) (hHL y)
  have hgmaps (t z : ℝ) (hz : z ∈ V) : g t z ∈ V := by
    by_contra hnot
    have hfix := hgOutside t (g t z) hnot
    have heq : g t z = z := (g t).injective hfix
    apply hnot
    rw [heq]
    exact hz
  have hFix (t : ℝ) (y : E3) (hy : (L y).2 ∉ V) : K t y = y := by
    rw [hK]
    simp only [hgOutside t (L y).2 hy, (Phi (L y).2).apply_symm_apply,
      Prod.eta, L.symm_apply_apply]
  have hMem (t : ℝ) (y : E3) : K t y ∈ surface ↔ y ∈ surface := by
    by_cases hy : (L y).2 ∈ V
    · have hLeft := hBand (g t (L y).2) (hgmaps t (L y).2 hy)
        ((Phi (L y).2).symm (L y).1)
      have hRight := hBand (L y).2 hy ((Phi (L y).2).symm (L y).1)
      rw [hK]
      change L.symm (Phi (g t (L y).2) ((Phi (L y).2).symm (L y).1),
        g t (L y).2) ∈ surface ↔ y ∈ surface
      calc
        _ ↔ L.symm ((Phi (L y).2).symm (L y).1, c0) ∈ surface := hLeft
        _ ↔ L.symm (L y) ∈ surface := by
          simpa only [(Phi (L y).2).apply_symm_apply, Prod.eta] using hRight.symm
        _ ↔ y ∈ surface := by rw [L.symm_apply_apply]
    · rw [hFix t y hy]
  have hMemInv (t : ℝ) (y : E3) : (K t).symm y ∈ surface ↔ y ∈ surface := by
    simpa only [(K t).apply_symm_apply] using (hMem t ((K t).symm y)).symm
  have hImage (t : ℝ) : K t '' surface = surface := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hMem t x).mpr hx
    · intro y hy
      exact ⟨(K t).symm y, (hMemInv t y).mpr hy, (K t).apply_symm_apply y⟩
  have hImageInv (t : ℝ) : (K t).symm '' surface = surface := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hMemInv t x).mpr hx
    · intro y hy
      exact ⟨K t y, (hMem t y).mpr hy, (K t).symm_apply_apply y⟩
  have hFixBoth (t : ℝ) (y : E3) (hy : ⟪(u : E3), y⟫_ℝ ∉ V) :
      K t y = y ∧ (K t).symm y = y := by
    have hfix : K t y = y := hFix t y (by simpa only [hHL y] using hy)
    refine ⟨hfix, ?_⟩
    have hh := congrArg (K t).symm hfix
    simpa only [(K t).symm_apply_apply] using hh.symm
  have hZero (y : E3) : K 0 y = y := by
    rw [hK]
    simp only [hg0, (Phi (L y).2).apply_symm_apply, Prod.eta,
      L.symm_apply_apply]
  exact ⟨K, hKs, hKis, hK, hKi, hHeight, hMem, hMemInv,
    fun t => ⟨hImage t, hImageInv t⟩, hFixBoth, hZero⟩

end PoincareConjecture.M25.Topology3D
