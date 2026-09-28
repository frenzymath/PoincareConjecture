import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperCoreLabel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperCapBandTube
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D





theorem exists_saddle_upper_leg
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) (z : ℝ)
    (hcz : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < z)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      z < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = z}) :
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let c := f D.point
    ∃ (i : Fin D.capCount) (eta : ℝ)
      (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere),
    let C := D.cap i
    let ell := C.cutHeight - C.removal
    C.sign = -1 ∧ (∀ k : Fin D.capCount, (D.cap k).sign = -1 ↔ k = i) ∧
    0 < eta ∧ eta < (z - c) / 4 ∧ eta < (ell - z) / 8 ∧
    Q.source = (univ : Set UnitCircle) ×ˢ Ioo (z - eta) (ell + eta) ∧
    Q.target = {q : UnitTwoSphere | f q ∈ Ioo (z - eta) (ell + eta)} ∧
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source ∧
    ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target ∧
    (∀ p ∈ Q.source, f (Q p) = p.2) ∧
    (∀ q ∈ Q.target, (Q.symm q).2 = f q) ∧
    (∀ theta : UnitCircle, psi (Q (theta, ell), 0) = C.tube (theta.1, ell)) ∧
    range (fun theta : UnitCircle => Q (theta, ell)) = C.sourceSeam ∧
    (∀ t ∈ Ioo (z - eta) (ell + eta),
      range (fun theta : UnitCircle => Q (theta, t)) = {q | f q = t}) ∧
    Q '' ((univ : Set UnitCircle) ×ˢ Icc z ell) =
      D.sourceCore ∩ {q | z ≤ f q} ∧
    C.sourceCap ∪ Q '' ((univ : Set UnitCircle) ×ˢ Icc z ell) =
      {q : UnitTwoSphere | z ≤ f q} ∧
    (∀ q : UnitTwoSphere, f q ∈ Icc z ell → q ∈ D.sourceCore ∧
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  change c < z at hcz
  obtain ⟨i, hsign, hunique, hz, hband, hseam, hcap, hreg⟩ :=
    exists_saddle_upper_core_label psi hpsi u D z hcz hseams hlevel
  let C := D.cap i
  let ell := C.cutHeight - C.removal
  change C.sign = -1 at hsign
  change z < ell at hz
  change {q : UnitTwoSphere | f q ∈ Icc z ell} =
    D.sourceCore ∩ {q | z ≤ f q} at hband
  change {q : UnitTwoSphere | f q = ell} = C.sourceSeam at hseam
  change C.sourceCap ∪ (D.sourceCore ∩ {q | z ≤ f q}) = {q | z ≤ f q} at hcap
  have hregular (q : UnitTwoSphere) (hq : f q ∈ Icc z ell) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := hreg q (hband ▸ hq)
  obtain ⟨r, gamma, o, w, T, hr, hg, hgap, _, _, _, _, _, _, _, hTs,
      hT, hTi, hTh, _, hTold, _, _, _, hcircle⟩ :=
    exists_saddle_upper_cap_band_tube psi hpsi u C hsign z hz hseam hregular
  let eta := min (gamma / 2) ((z - c) / 8)
  have heta : 0 < eta := lt_min (div_pos hg (by norm_num))
    (div_pos (sub_pos.mpr hcz) (by norm_num))
  have hetag : eta < gamma := by
    have hh : eta ≤ gamma / 2 := min_le_left _ _
    linarith
  have hetac : eta < (z - c) / 4 := by
    have hh : eta ≤ (z - c) / 8 := min_le_right _ _
    linarith
  have hetagap : eta < (ell - z) / 8 := hetag.trans hgap
  let J := Ioo (z - eta) (ell + eta)
  have hJsub (t : ℝ) (ht : t ∈ J) : t ∈ Icc (z - gamma) (ell + gamma) := by
    constructor <;> linarith [ht.1, ht.2]
  have hclosedJ (t : ℝ) (ht : t ∈ Icc z ell) : t ∈ J := by
    constructor <;> linarith [ht.1, ht.2]
  have hcircleS (theta : UnitCircle) (t : ℝ) (ht : t ∈ J) : T (theta.1, t) ∈ range j := by
    have hm : T (theta.1, t) ∈ T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) :=
      ⟨(theta.1, t), ⟨theta.2, mem_singleton _⟩, rfl⟩
    exact ((hcircle t (hJsub t ht)) ▸ hm).1
  obtain ⟨Q, hQs, hQ, hQi, hQpoint⟩ := exists_source_tube_chart psi hpsi T hT hTi
    isOpen_Ioo (fun p hp => hTs ⟨sphere_subset_closedBall hp.1, mem_univ _⟩) hcircleS
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hQh (p : UnitCircle × ℝ) (hp : p ∈ Q.source) : f (Q p) = p.2 := by
    change ⟪(u : E3), psi (Q p, 0)⟫_ℝ = p.2
    rw [hQpoint p.1 p.2 (hQs ▸ hp).2]
    exact hTh _ (hTs ⟨sphere_subset_closedBall p.1.2, mem_univ _⟩)
  have hQlevel (t : ℝ) (ht : t ∈ J) :
      range (fun theta : UnitCircle => Q (theta, t)) = {q | f q = t} := by
    ext q
    constructor
    · rintro ⟨theta, rfl⟩
      exact hQh (theta, t) (hQs.symm ▸ ⟨mem_univ _, ht⟩)
    · intro hq
      have hm : j q ∈ T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) :=
        (hcircle t (hJsub t ht)).symm ▸ ⟨mem_range_self q, hq⟩
      obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, hxy⟩ := hm
      have hst : s = t := hs
      subst s
      exact ⟨⟨x, hx⟩, hji ((hQpoint ⟨x, hx⟩ t ht).trans hxy)⟩
  have hQt : Q.target = {q : UnitTwoSphere | f q ∈ J} := by
    ext q
    constructor
    · intro hq
      have hp := Q.map_target hq
      have hh := hQh (Q.symm q) hp
      rw [Q.right_inv hq] at hh
      change f q ∈ J
      rw [hh]
      exact (hQs ▸ hp).2
    · intro hq
      have hm : q ∈ range (fun theta : UnitCircle => Q (theta, f q)) :=
        (hQlevel (f q) hq).symm ▸ rfl
      obtain ⟨theta, htheta⟩ := hm
      rw [← htheta]
      exact Q.map_source (hQs.symm ▸ ⟨mem_univ _, hq⟩)
  have hQih (q : UnitTwoSphere) (hq : q ∈ Q.target) : (Q.symm q).2 = f q := by
    have hh := hQh (Q.symm q) (Q.map_target hq)
    rw [Q.right_inv hq] at hh
    exact hh.symm
  have hellJ : ell ∈ J := hclosedJ ell ⟨hz.le, le_rfl⟩
  have hQold (theta : UnitCircle) : psi (Q (theta, ell), 0) = C.tube (theta.1, ell) := by
    rw [hQpoint theta ell hellJ]
    have hsource : (theta.1, ell) ∈ C.tube.source :=
      C.tube_source (a := (theta.1, ell)) ⟨sphere_subset_closedBall theta.2, mem_univ _⟩
    exact (hTold (theta.1, ell) hsource
      (by simpa only [norm_eq_of_mem_sphere theta] using hr) (by linarith)).1
  have hQband : Q '' ((univ : Set UnitCircle) ×ˢ Icc z ell) =
      {q : UnitTwoSphere | f q ∈ Icc z ell} := by
    ext q
    constructor
    · rintro ⟨⟨theta, t⟩, ⟨_, ht⟩, rfl⟩
      have hs : (theta, t) ∈ Q.source := hQs.symm ▸ ⟨mem_univ _, hclosedJ t ht⟩
      change f (Q (theta, t)) ∈ Icc z ell
      rw [hQh _ hs]
      exact ht
    · intro hq
      have hm : q ∈ range (fun theta : UnitCircle => Q (theta, f q)) :=
        (hQlevel (f q) (hclosedJ (f q) hq)).symm ▸ rfl
      obtain ⟨theta, htheta⟩ := hm
      exact ⟨(theta, f q), ⟨mem_univ _, hq⟩, htheta⟩
  have hQcore : Q '' ((univ : Set UnitCircle) ×ˢ Icc z ell) =
      D.sourceCore ∩ {q | z ≤ f q} := hQband.trans hband
  refine ⟨i, eta, Q, hsign, hunique, heta, hetac, hetagap, hQs, hQt,
    hQ, hQi, hQh, hQih, hQold, (hQlevel ell hellJ).trans hseam,
    hQlevel, hQcore, ?_, ?_⟩
  · rw [hQcore]
    exact hcap
  · intro q hq
    have hcore : q ∈ D.sourceCore ∩ {q | z ≤ f q} :=
      hband ▸ (show q ∈ {q : UnitTwoSphere | f q ∈ Icc z ell} from hq)
    exact ⟨hcore.1, hregular q hq⟩

end PoincareConjecture.M25.Topology3D
