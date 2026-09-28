import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularSourceLevelFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RawPieceBandInput
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallNoBypass
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SourceCircleCut
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_lower_level_count
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let c : ℝ := f D.point
    ∃ R delta : ℝ, ∃ N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      0 < R ∧ 0 < delta ∧ delta < epsilon ∧
      delta ≤ (5 * R / 8) ^ 2 / 128 ∧
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆ D.morse.target ∧
      (∀ p : UnitTwoSphere, |f p - c| ≤ 3 * delta → p ∈ D.sourceCore) ∧
      (∀ s : ℝ × ℝ,
        N (N s) = s ∧
        (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
        D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
          s.1 ^ 2 - s.2 ^ 2) ∧
      (∀ p : UnitTwoSphere, f p = c - delta →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0) ∧
      ∃ n : ℕ, ∃ q : Fin n → UnitCircle → UnitTwoSphere,
        (n = 1 ∨ n = 2) ∧
        (∀ i : Fin n,
          ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
          ∀ theta : UnitCircle,
            Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
        (∀ i k : Fin n, i ≠ k → Disjoint (range (q i)) (range (q k))) ∧
        (⋃ i : Fin n, range (q i)) = {p : UnitTwoSphere | f p = c - delta} := by
  classical
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let c := f D.point
  obtain ⟨R, b, P, _A, hR, _hb, hPs, _hAs, _hPsm, _hPi, _hAsm, _hAi,
    hPm, _hPf, _hP0, _hA0, _hAt, _hAf, _hAinv, _hBR, _hBA, _hcoords,
    _hcaps, hcore, _hregular⟩ := exists_raw_saddle_piece_band_input psi hpsi u D
  have hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target := by simpa only [hPs] using hPm
  let rho := 5 * R / 8
  have hrho : 0 < rho := by dsimp [rho]; positivity
  let delta := min (epsilon / 2) (min b (rho ^ 2 / 128))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdE : delta ≤ epsilon / 2 := min_le_left _ _
  have hdB : delta ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hdR : delta ≤ rho ^ 2 / 128 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hdsmall : delta < rho ^ 2 := by nlinarith [sq_pos_of_pos hrho]
  have hcoreBand (p : UnitTwoSphere) (hp : |f p - c| ≤ 3 * delta) :
      p ∈ D.sourceCore := hcore p (by change |f p - c| ≤ 8 * b; linarith)
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Q : ℝ × ℝ → ℝ := fun s =>
    D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
  have hsign : D.morseSign1 = 1 ∨ D.morseSign1 = -1 :=
    mul_self_eq_one_iff.mp D.morseSign1_sq
  let N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := if D.morseSign1 = 1 then
    ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) else ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hN (s : ℝ × ℝ) : N (N s) = s ∧ r2 (N s) = r2 s ∧
      Q (N s) = s.1 ^ 2 - s.2 ^ 2 := by
    rcases hsign with h | h <;>
      norm_num [N, h, r2, Q, D.morseSigns_opposite, add_comm] <;> ring
  have hreg (p : UnitTwoSphere) (hp : f p = c - delta) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
    have hpcore : p ∈ D.sourceCore := hcoreBand p (by
      rw [hp, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
      linarith)
    intro hcritical
    have heq : p = D.point := (D.unique_critical p hpcore).mp hcritical
    subst p
    change c = c - delta at hp
    linarith
  obtain ⟨n, q, _e, hq, hdisjoint, hlevel, _hcomponents⟩ :=
    exists_regular_source_level_family psi hpsi (u : E3) (c - delta) hreg
  refine ⟨R, delta, N, hR, hd, by linarith, hdR, hmorse, hcoreBand, hN,
    hreg, n, q, ?_, hq, hdisjoint, hlevel⟩
  let Bc : Set (ℝ × ℝ) := {s | r2 s ≤ rho ^ 2}
  let Bo : Set (ℝ × ℝ) := {s | r2 s < rho ^ 2}
  let m : ℝ × ℝ → UnitTwoSphere := fun s => D.morse.symm (N s)
  let Dc : Set UnitTwoSphere := D.morse.symm '' Bc
  let V : Set UnitTwoSphere := D.morse.symm '' Bo
  let La : Set UnitTwoSphere := {p | f p = c - delta}
  change (⋃ i : Fin n, range (q i)) = La at hlevel
  have hBoBc : Bo ⊆ Bc := fun s hs => (show r2 s < rho ^ 2 from hs).le
  have hNs (s : ℝ × ℝ) (hs : s ∈ Bc) : N s ∈ D.morse.target := by
    apply hmorse
    change r2 (N s) < (2 * R) ^ 2
    rw [(hN s).2.1]
    change r2 s ≤ rho ^ 2 at hs
    dsimp [rho] at hs
    nlinarith [sq_pos_of_pos hR]
  have hmcont : ContinuousOn m Bc :=
    D.morse.symm.continuousOn.comp N.continuous.continuousOn (fun s hs => hNs s hs)
  have hminj : InjOn m Bc := by
    intro s hs t ht hst
    exact N.injective (D.morse.symm.injOn (hNs s hs) (hNs t ht) hst)
  have hmheight (s : ℝ × ℝ) (hs : s ∈ Bc) :
      f (m s) = c + (s.1 ^ 2 - s.2 ^ 2) := by
    have hh := D.morse_height (m s) (D.morse.map_target (hNs s hs))
    change f (m s) = c + D.morseSign1 * (D.morse (m s)).1 ^ 2 +
      D.morseSign2 * (D.morse (m s)).2 ^ 2 at hh
    have hmrec : D.morse (m s) = N s := D.morse.right_inv (hNs s hs)
    rw [hmrec] at hh
    have hn := (hN s).2.2
    dsimp [Q] at hn
    linarith
  have hnormalize (Z : Set (ℝ × ℝ)) (hZ : ∀ s, s ∈ Z ↔ N s ∈ Z) :
      D.morse.symm '' Z = m '' Z := by
    ext p
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨N s, (hZ s).mp hs, ?_⟩
      change D.morse.symm (N (N s)) = D.morse.symm s
      rw [(hN s).1]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨N s, (hZ s).mp hs, rfl⟩
  have hDc : Dc = m '' Bc := hnormalize Bc (fun s => by
    change r2 s ≤ rho ^ 2 ↔ r2 (N s) ≤ rho ^ 2; rw [(hN s).2.1])
  have hV : V = m '' Bo := hnormalize Bo (fun s => by
    change r2 s < rho ^ 2 ↔ r2 (N s) < rho ^ 2; rw [(hN s).2.1])
  have hcut (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ Bc) :
      La ∩ m '' Z =
        m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧ s ∈ Z} := by
    ext p
    constructor
    · rintro ⟨hp, s, hs, rfl⟩
      refine ⟨s, ⟨?_, hs⟩, rfl⟩
      have hh := hmheight s (hZ hs)
      change f (m s) = c - delta at hp
      linarith
    · rintro ⟨s, ⟨ht, hs⟩, rfl⟩
      refine ⟨?_, ⟨s, hs, rfl⟩⟩
      change f (m s) = c - delta
      rw [hmheight s (hZ hs), ht]
      ring
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let lo : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
  let pm : Fin 4 → ℝ × ℝ := fun i => (sx i * aa, sy i * bb)
  obtain ⟨hlocal, hldis, hlclosed, hlopen, _huclosed, hends⟩ :=
    saddle_hyperbola_disc_arcs rho delta hrho hd hdsmall
  have hlo (i : Fin 2) (t : unitInterval) :
      (lo i t).1 ^ 2 - (lo i t).2 ^ 2 = -delta ∧ lo i t ∈ Bc := by
    change lo i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    rw [hlclosed]
    exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (lo i t)
  let p : Fin 4 → UnitTwoSphere := fun i => m (pm i)
  have hgamma (i : Fin 2) : Continuous (gamma i) ∧ Injective (gamma i) := by
    refine ⟨hmcont.comp_continuous (hlocal i).1 (fun t => (hlo i t).2), ?_⟩
    intro s t hst
    exact (hlocal i).2.1 (hminj (hlo i s).2 (hlo i t).2 hst)
  have hgdis : Disjoint (range (gamma 0)) (range (gamma 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    have heq : lo 1 t = lo 0 s := hminj (hlo 1 t).2 (hlo 0 s).2 ht
    exact disjoint_left.mp hldis ⟨s, rfl⟩ ⟨t, heq⟩
  have hgend (i : Fin 2) : gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))) :=
    ⟨congrArg m (hends i).1, congrArg m (hends i).2.1⟩
  have hnegative : La ∩ Dc = ⋃ i : Fin 2, range (gamma i) := by
    have hh := hcut Bc (Subset.refl Bc)
    rw [← hDc] at hh
    change La ∩ Dc = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} at hh
    rw [hlclosed, image_iUnion] at hh
    apply hh.trans
    apply iUnion_congr
    intro i
    change m '' range (lo i) = range (m ∘ lo i)
    exact (Set.range_comp m (lo i)).symm
  have hnegativeOpen : La ∩ V = ⋃ i : Fin 2,
      gamma i '' Ioo (0 : unitInterval) 1 := by
    have hh := hcut Bo hBoBc
    rw [← hV] at hh
    change La ∩ V = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} at hh
    rw [hlopen, image_iUnion] at hh
    simpa only [image_image] using hh
  have hqLa (i : Fin n) : range (q i) ⊆ La := by
    intro x hx
    rw [← hlevel]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hqCompact (i : Fin n) : IsCompact (range (q i)) :=
    isCompact_range (hq i).1.continuous
  have hcomplement (i : Fin n) :
      La \ range (q i) = ⋃ k : {k : Fin n // k ≠ i}, range (q k.1) := by
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      rw [← hlevel] at hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      have hki : k ≠ i := by intro heq; subst k; exact hnot hk
      exact mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact ⟨hqLa k.1 hk, fun hi => disjoint_left.mp (hdisjoint k.1 i k.2) hk hi⟩
  have hnoBypass (i : Fin n) : ¬ Disjoint (range (q i)) Dc := by
    intro hi
    have hcomp : IsCompact (La \ range (q i)) := by
      rw [hcomplement i]
      exact isCompact_iUnion (fun k => hqCompact k.1)
    have hempty : range (q i) = ∅ :=
      saddle_selected_wall_no_bypass psi hpsi u D R delta hR hd hdR hmorse hcoreBand
        N hN (range (q i)) (hqLa i) (hqCompact i) hcomp hi
    have hnonempty : (range (q i)).Nonempty :=
      ⟨q i (circleDirection (0 : E2)), circleDirection (0 : E2), rfl⟩
    exact hnonempty.ne_empty hempty
  obtain ⟨removedParent, _arcParent, _a, _v, _ends, _eta, _hpi, _heta, _hetaSmall,
    _hparent, _harcs, _harcsDisjoint, _harcBypass, hbiff, _hcover, _hrim, hcard,
    _hdifferent, _hsame⟩ :=
    exists_saddle_source_circle_cut n q hq hdisjoint gamma hgamma hgdis p hgend V Dc
      (by rw [hlevel]; exact hnegative) (by rw [hlevel]; exact hnegativeOpen)
  let bypass : Finset (Fin n) := Finset.univ \ {removedParent 0, removedParent 1}
  change (∀ i : Fin n, i ∈ bypass ↔ Disjoint (range (q i)) Dc) at hbiff
  have hbempty : bypass = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hnoBypass i ((hbiff i).mp hi)
  change bypass.card + (if removedParent 0 = removedParent 1 then 1 else 2) = n at hcard
  by_cases hsame : removedParent 0 = removedParent 1
  · left
    simpa only [hbempty, Finset.card_empty, hsame, ite_true, zero_add] using hcard.symm
  · right
    simpa only [hbempty, Finset.card_empty, hsame, ite_false, zero_add] using hcard.symm

end PoincareConjecture.M25.Topology3D
