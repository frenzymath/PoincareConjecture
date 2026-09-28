import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleExteriorPortMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleSourceDiscGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SourceCircleCut

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_one_circle_exterior_matching
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R delta : ℝ) (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hR : 0 < R) (hd : 0 < delta)
    (hdR : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆ D.morse.target)
    (hcore : ∀ p : UnitTwoSphere,
      |⟪(u : E3), psi (p, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → p ∈ D.sourceCore)
    (hN : ∀ s : ℝ × ℝ, N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2)
    (q : Fin 1 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Injective (q i) ∧
      ∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta))
    (hlevel : (⋃ i, range (q i)) = {p | ⟪(u : E3), psi (p, 0)⟫_ℝ =
      ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta}) :
    let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let c := f D.point
    let r := 5 * R / 8
    let Dc := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    let aa := Real.sqrt ((r ^ 2 - delta) / 2)
    let bb := Real.sqrt ((r ^ 2 + delta) / 2)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let pm : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * aa, sy i * bb))
    ∃ (alpha : Fin 2 → ℝ → UnitTwoSphere)
      (ends : Fin 2 × Fin 2 ≃ Fin 4) (label : Fin 2 ≃ Fin 2),
      (∀ k, Continuous (alpha k)) ∧
      Disjoint (alpha 0 '' Icc (0 : ℝ) 1) (alpha 1 '' Icc (0 : ℝ) 1) ∧
      {p | f p = c - delta} \ Do = ⋃ k, alpha k '' Icc (0 : ℝ) 1 ∧
      (∀ k, (alpha k '' Icc (0 : ℝ) 1) ∩ Dc =
        {pm (ends (k, 0)), pm (ends (k, 1))}) ∧
      ∀ k, ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {finProdFinEquiv (label k, (0 : Fin 2)),
          finProdFinEquiv ((![1, 0] : Fin 2 → Fin 2) (label k), (1 : Fin 2))} := by
  classical
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let c := f D.point
  let r := 5 * R / 8
  let Dc := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
  let Do := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  let aa := Real.sqrt ((r ^ 2 - delta) / 2)
  let bb := Real.sqrt ((r ^ 2 + delta) / 2)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let pm : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * aa, sy i * bb))
  obtain ⟨gm, _gp, hgm, hgdis, _hgpdis, hends, hclosed, hopen, _hpositive⟩ :=
    saddle_source_disc_arc_geometry psi u D R delta N hR hd hdR hmorse hN
  obtain ⟨removedParent, arcParent, a, v, ends, eta, _hpi, heta, _hetaSmall,
    _hparent, harcs, harcsDisjoint, _harcBypass, _hbiff, hcover, _hrim, _hcard,
    _hdifferent, hsame⟩ :=
    exists_saddle_source_circle_cut 1 q hq
      (fun i k hik => False.elim (hik (Subsingleton.elim i k))) gm
      (fun i => ⟨(hgm i).1, (hgm i).2.1⟩) hgdis pm
      (fun i => ⟨(hends i).1, (hends i).2.1⟩) Do Dc
      (by rw [hlevel]; exact hclosed) (by rw [hlevel]; exact hopen)
  let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
    q (arcParent k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
  have hasmooth (k : Fin 2) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha k) ∧
      ∀ t, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha k) t) :=
    ⟨(harcs k).2.2.1, (harcs k).2.2.2.1⟩
  have halevel (k : Fin 2) (t : ℝ) : f (alpha k t) = c - delta := by
    have hh : alpha k t ∈ ⋃ i, range (q i) :=
      mem_iUnion.mpr ⟨arcParent k, _, rfl⟩
    rw [hlevel] at hh
    exact hh
  have hend (k : Fin 2) : alpha k 0 = pm (ends (k, 0)) ∧
      alpha k 1 = pm (ends (k, 1)) :=
    ⟨(harcs k).2.2.2.2.2.1, (harcs k).2.2.2.2.2.2.1⟩
  have hout (k : Fin 2) : Disjoint (alpha k '' Ioo (0 : ℝ) 1) Dc :=
    (harcs k).2.2.2.2.2.2.2.1
  have hinc (k : Fin 2) : (alpha k '' Icc (0 : ℝ) 1) ∩ Dc =
      {pm (ends (k, 0)), pm (ends (k, 1))} := (harcs k).2.2.2.2.2.2.2.2.1
  have hafter (k : Fin 2) : ∀ t ∈ Ioo (1 : ℝ) (1 + eta), alpha k t ∈ Do :=
    (harcs k).2.2.2.2.2.2.2.2.2.2
  obtain ⟨label, hlabel⟩ := exists_saddle_exterior_upper_matching psi hpsi u D
    R delta N hR hd hdR hmorse hcore hN alpha hasmooth halevel ends eta heta
    hend hout hafter (hsame (Subsingleton.elim _ _)).2
  let bypass : Finset (Fin 1) := Finset.univ \ {removedParent 0, removedParent 1}
  have hbempty : bypass = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hin : i ∈ ({removedParent 0, removedParent 1} : Finset (Fin 1)) := by
      simp [Subsingleton.elim i (removedParent 0)]
    exact (Finset.mem_sdiff.mp hi).2 hin
  have hcover' : {p | f p = c - delta} \ Do =
      ⋃ k, alpha k '' Icc (0 : ℝ) 1 := by
    change (⋃ i, range (q i)) \ Do = (⋃ k, alpha k '' Icc (0 : ℝ) 1) ∪
      (⋃ j ∈ bypass, range (q j)) at hcover
    simpa [hlevel, hbempty] using hcover
  have hsmall : Icc (0 : ℝ) 1 ⊆ Icc (-eta) (1 + eta) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨alpha, ends, label, fun k => (hasmooth k).1.continuous,
    harcsDisjoint.mono (image_mono hsmall) (image_mono hsmall),
    hcover', hinc, hlabel⟩

end PoincareConjecture.M25.Topology3D
