import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RawPieceBandInput
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerLevelTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedTwoExteriorArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceSurfacePullback
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import Mathlib.Tactic









set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_connected_upper_level
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let c := f D.point
    ∃ delta : ℝ,
      0 < delta ∧ delta < epsilon ∧ delta < c - W.level ∧
      (∀ q : UnitTwoSphere, |f q - c| ≤ 3 * delta → q ∈ D.sourceCore) ∧
      (∀ i : Fin D.capCount, (D.cap i).sign = -1 →
        c + 3 * delta < (D.cap i).cutHeight +
          (D.cap i).sign * (D.cap i).removal) ∧
      IsConnected {q : UnitTwoSphere | f q = c + delta} := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), j q⟫_ℝ
  let c := f D.point
  let S : Set E3 := range j
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j := collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  obtain ⟨R, b, P, A, hR, hb, hPs, _hAs, _hPsm, _hPi, _hAsm, _hAi,
    hPm, _hPf, _hP0, _hA0, _hAt, _hAf, _hAinv, _hBR, _hBA, _hcoords,
    hcaps, hcore, _hregular⟩ := exists_raw_saddle_piece_band_input psi hpsi u D
  have hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target := by simpa only [hPs] using hPm
  let rho := 5 * R / 8
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hgap : 0 < c - W.level := sub_pos.mpr W.level_lt_critical
  let delta := min (epsilon / 2) (min b (min ((c - W.level) / 2) (rho ^ 2 / 128)))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdE : delta ≤ epsilon / 2 := min_le_left _ _
  have hdB : delta ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hdW : delta ≤ (c - W.level) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdR : delta ≤ rho ^ 2 / 128 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdsmall : delta < rho ^ 2 := by nlinarith [sq_pos_of_pos hrho]
  have hcoreBand (q : UnitTwoSphere) (hq : |f q - c| ≤ 3 * delta) :
      q ∈ D.sourceCore := hcore q (by change |f q - c| ≤ 8 * b; linarith)
  let seam : Fin D.capCount → ℝ := fun i =>
    (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal
  have hseamheight (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap i).sourceSeam) : f q = seam i := by
    obtain ⟨p, hp, rfl⟩ := hq
    change (heightCoordinates (p : E3)).2 = 0 at hp
    let C := D.cap i
    have hm : (C.profile.model p).2 = 0 := by
      have hh := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far p (by rw [hp]; norm_num)
      simpa only [SurgeryCapProfile.model, hp] using congrArg Prod.snd hh
    have hT : ((C.profile.model p).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model p).2)) ∈
        C.tube.source := C.tube_source
      ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le p), mem_univ _⟩
    change ⟪(u : E3), psi (C.sourceChart p, 0)⟫_ℝ =
      C.cutHeight + C.sign * C.removal
    rw [C.central_eq p (by rw [hp]; exact C.overlap_pos),
      SurgeryCapProfile.capMap_apply, C.tube_height _ hT, hm, mul_zero, add_zero]
  have hupper (i : Fin D.capCount) (hi : (D.cap i).sign = -1) :
      c + 3 * delta < seam i := by
    have hcut : c < (D.cap i).cutHeight := by
      rcases D.cut_side i with ⟨hs, _⟩ | ⟨_, hs⟩
      · rw [hi] at hs; norm_num at hs
      · exact hs
    have hcutgap := D.cutRadius_lt_gap i
    change D.cutRadius i < |(D.cap i).cutHeight - c| at hcutgap
    rw [abs_of_pos (sub_pos.mpr hcut)] at hcutgap
    have hsc : c < seam i := by
      dsimp [seam]; rw [hi]; nlinarith [D.removal_lt_cutRadius i]
    obtain ⟨q, hq⟩ := (D.cap i).sourceSeam_isConnected.nonempty
    have hqcap : q ∈ (D.cap i).sourceCap := by
      obtain ⟨p, hp, rfl⟩ := hq
      exact ⟨p, hp.le, rfl⟩
    have hh := hcaps i (j q) ⟨q, hqcap, rfl⟩
    change 8 * b < |f q - c| at hh
    rw [hseamheight i q hq, abs_of_pos (sub_pos.mpr hsc)] at hh
    linarith
  refine ⟨delta, hd, by linarith, by linarith, hcoreBand, hupper, ?_⟩
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
  let Bc : Set (ℝ × ℝ) := {s | r2 s ≤ rho ^ 2}
  let Bo : Set (ℝ × ℝ) := {s | r2 s < rho ^ 2}
  let m : ℝ × ℝ → UnitTwoSphere := fun s => D.morse.symm (N s)
  let Dc : Set UnitTwoSphere := D.morse.symm '' Bc
  let V : Set UnitTwoSphere := D.morse.symm '' Bo
  let Lm : Set UnitTwoSphere := {q | f q = c - delta}
  let Lp : Set UnitTwoSphere := {q | f q = c + delta}
  have hBoBc : Bo ⊆ Bc := by
    intro s hs
    exact (show r2 s < rho ^ 2 from hs).le
  have hVD : V ⊆ Dc := image_mono hBoBc
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
    ext q
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
  have hcut (t : ℝ) (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ Bc) :
      {q : UnitTwoSphere | f q = c + t} ∩ m '' Z =
        m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = t ∧ s ∈ Z} := by
    ext q
    constructor
    · rintro ⟨hq, s, hs, rfl⟩
      refine ⟨s, ⟨?_, hs⟩, rfl⟩
      have hh := hmheight s (hZ hs)
      change f (m s) = c + t at hq
      linarith
    · rintro ⟨s, ⟨ht, hs⟩, rfl⟩
      refine ⟨?_, ⟨s, hs, rfl⟩⟩
      change f (m s) = c + t
      rw [hmheight s (hZ hs), ht]
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let other : Fin 2 → Fin 2 := ![1, 0]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let lo : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
  let up : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * Real.sqrt ((vv t) ^ 2 + delta), sg i * vv t)
  let pm : Fin 4 → ℝ × ℝ := fun i => (sx i * aa, sy i * bb)
  let pp : Fin 4 → ℝ × ℝ := fun i => (sx i * bb, sy i * aa)
  obtain ⟨hlocal, hldis, hlclosed, hlopen, huclosed, hends⟩ :=
    saddle_hyperbola_disc_arcs rho delta hrho hd hdsmall
  have hlo (i : Fin 2) (t : unitInterval) :
      (lo i t).1 ^ 2 - (lo i t).2 ^ 2 = -delta ∧ lo i t ∈ Bc := by
    change lo i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    rw [hlclosed]
    exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  have hup (i : Fin 2) (t : unitInterval) :
      (up i t).1 ^ 2 - (up i t).2 ^ 2 = delta ∧ up i t ∈ Bc := by
    change up i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    rw [huclosed]
    exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (lo i t)
  let beta : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (up i t)
  let p : Fin 4 → UnitTwoSphere := fun i => m (pm i)
  let pplus : Fin 4 → UnitTwoSphere := fun i => m (pp i)
  have hgamma (i : Fin 2) : Continuous (gamma i) ∧ Injective (gamma i) := by
    refine ⟨hmcont.comp_continuous (hlocal i).1 (fun t => (hlo i t).2), ?_⟩
    intro s t hst
    exact (hlocal i).2.1 (hminj (hlo i s).2 (hlo i t).2 hst)
  have hbeta (i : Fin 2) : Continuous (beta i) :=
    hmcont.comp_continuous (hlocal i).2.2.1 (fun t => (hup i t).2)
  have hgdis : Disjoint (range (gamma 0)) (range (gamma 1)) := by
    apply disjoint_left.mpr
    rintro q ⟨s, rfl⟩ ⟨t, ht⟩
    have heq : lo 1 t = lo 0 s := hminj (hlo 1 t).2 (hlo 0 s).2 ht
    exact disjoint_left.mp hldis ⟨s, rfl⟩ ⟨t, heq⟩
  have hgend (i : Fin 2) : gamma i 0 = p (ep (i, 0)) ∧
      gamma i 1 = p (ep (i, 1)) :=
    ⟨congrArg m (hends i).1, congrArg m (hends i).2.1⟩
  have hbend (i : Fin 2) : beta i 0 = pplus (ep (i, 0)) ∧
      beta i 1 = pplus (ep (other i, 1)) :=
    ⟨congrArg m (hends i).2.2.1, congrArg m (hends i).2.2.2⟩
  have hnegative : Lm ∩ Dc = ⋃ i : Fin 2, range (gamma i) := by
    have hh := hcut (-delta) Bc (Subset.refl Bc)
    rw [← hDc] at hh
    have hc : c + -delta = c - delta := by ring
    rw [hc] at hh
    change Lm ∩ Dc = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} at hh
    rw [hlclosed, image_iUnion] at hh
    apply hh.trans
    apply iUnion_congr
    intro i
    change m '' range (lo i) = range (m ∘ lo i)
    exact (Set.range_comp m (lo i)).symm
  have hnegativeOpen : Lm ∩ V = ⋃ i : Fin 2,
      gamma i '' Ioo (0 : unitInterval) 1 := by
    have hh := hcut (-delta) Bo hBoBc
    rw [← hV] at hh
    have hc : c + -delta = c - delta := by ring
    rw [hc] at hh
    change Lm ∩ V = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} at hh
    rw [hlopen, image_iUnion] at hh
    simpa only [image_image] using hh
  have hpositive : Lp ∩ Dc = ⋃ i : Fin 2, range (beta i) := by
    have hh := hcut delta Bc (Subset.refl Bc)
    rw [← hDc] at hh
    change Lp ∩ Dc = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} at hh
    rw [huclosed, image_iUnion] at hh
    apply hh.trans
    apply iUnion_congr
    intro i
    change m '' range (up i) = range (m ∘ up i)
    exact (Set.range_comp m (up i)).symm
  have hla : W.level ≤ c - delta := by linarith
  have hac : c - delta < c := by linarith
  obtain ⟨_hreg, _hc0, d, T, _hd, hI, _hTs, _hTi, _hT0, _hSupp,
    hC, hDis, _hMembership, hCover, _hCases⟩ :=
    exists_saddle_lower_level_transport psi hpsi u D W (c - delta) hla hac
  let C : Fin 2 → UnitCircle → E2 := fun i theta =>
    T (c - delta) (pi (j (W.leg i (theta, W.level))))
  let ca : Fin 2 → UnitCircle → E3 := fun i theta => L.symm (C i theta, c - delta)
  have hemb (i : Fin 2) : IsPlanarEmbedding (C i) := ((hC i).2 (c - delta)).1
  have hCa : {x : E2 | L.symm (x, c - delta) ∈ range j} =
      ⋃ i : Fin 2, range (C i) := by
    rw [hCover (c - delta) (hI ⟨hla, le_rfl⟩)]
    exact iUnion_congr (fun i => ((hC i).2 (c - delta)).2.symm)
  have hCadis : Disjoint (range (C 0)) (range (C 1)) := by
    rw [((hC 0).2 (c - delta)).2, ((hC 1).2 (c - delta)).2]
    exact hDis (c - delta)
  have hcaproj (i : Fin 2) : pi ∘ ca i = C i := by
    funext theta
    change (L (L.symm (C i theta, c - delta))).1 = C i theta
    rw [L.apply_symm_apply]
  have hcaproj_apply (i : Fin 2) (theta : UnitCircle) : pi (ca i theta) = C i theta :=
    congrFun (hcaproj i) theta
  have hlift (i : Fin 2) : ∃ q : UnitCircle → UnitTwoSphere,
      ContMDiff (𝓡 1) (𝓡 2) ∞ q ∧ Injective q ∧
      (∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) q theta)) ∧
      ∀ theta, j (q theta) = ca i theta := by
    have hcs : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ (ca i) :=
      L.symm.contDiff.contMDiff.comp ((hemb i).1.prodMk_space contMDiff_const)
    have hci : Injective (ca i) := by
      intro s t hst
      apply (hemb i).2.1
      simpa only [hcaproj_apply] using congrArg pi hst
    have hcd (theta : UnitCircle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (ca i) theta) := by
      have hpim : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ pi := pi.contDiff.contMDiff
      have hh := (hpim.mdifferentiable (by simp) (ca i theta)).hasMFDerivAt.comp
        theta (hcs.mdifferentiable (by simp) theta).hasMFDerivAt
      rw [hcaproj] at hh
      intro x y hxy
      apply (hemb i).2.2 theta
      rw [hh.mfderiv]
      exact congrArg (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E2) pi (ca i theta)) hxy
    have hcentral : MapsTo (ca i) univ (range j) := by
      intro theta _
      have ht : C i theta ∈ ⋃ k : Fin 2, range (C k) :=
        mem_iUnion.mpr ⟨i, ⟨theta, rfl⟩⟩
      rw [← hCa] at ht
      exact ht
    obtain ⟨q, hqs, hqi, hqd, hqr⟩ := exists_collar_surface_source_pullback
      (𝓡 1) psi hpsi (ca i) isOpen_univ hcs.contMDiffOn hci.injOn
      (fun theta _ => hcd theta) hcentral
    exact ⟨q, contMDiffOn_univ.mp hqs, fun x y h => hqi (mem_univ _) (mem_univ _) h,
      fun theta => hqd theta (mem_univ _), fun theta => hqr theta (mem_univ _)⟩
  choose q hqs hqi hqd hqr using hlift
  have hq (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Injective (q i) ∧
      ∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta) :=
    ⟨hqs i, hqi i, hqd i⟩
  have hqdis : Disjoint (range (q 0)) (range (q 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    have hh : C 1 t = C 0 s := by
      have hjj := congrArg j ht
      rw [hqr 1 t, hqr 0 s] at hjj
      simpa only [hcaproj_apply] using congrArg pi hjj
    exact disjoint_left.mp hCadis ⟨s, rfl⟩ ⟨t, hh⟩
  have hqpair (i k : Fin 2) (hik : i ≠ k) : Disjoint (range (q i)) (range (q k)) := by
    fin_cases i <;> fin_cases k <;>
      first | exact False.elim (hik rfl) | exact hqdis | exact hqdis.symm
  have hqlevel : (⋃ i : Fin 2, range (q i)) = Lm := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, theta, rfl⟩ := mem_iUnion.mp hx
      change ⟪(u : E3), j (q i theta)⟫_ℝ = c - delta
      rw [hqr, ← heightPlaneCoordinates_snd u]
      change (L (L.symm (C i theta, c - delta))).2 = c - delta
      rw [L.apply_symm_apply]
    · intro hx
      have hrec : L.symm (pi (j x), c - delta) = j x :=
        heightPlaneCoordinates_reconstruct u (j x) (c - delta) hx
      have hm : pi (j x) ∈ ⋃ i : Fin 2, range (C i) := by
        rw [← hCa]
        change L.symm (pi (j x), c - delta) ∈ range j
        rw [hrec]
        exact ⟨x, rfl⟩
      obtain ⟨i, theta, ht⟩ := mem_iUnion.mp hm
      refine mem_iUnion.mpr ⟨i, ⟨theta, hji ?_⟩⟩
      rw [hqr]
      change L.symm (C i theta, c - delta) = j x
      rw [ht, hrec]
  obtain ⟨label, a, v, ends, eta, _hp, _heta, _hetaSmall, _hparent, harcs,
    _haDis, hexterior, _hrim, hpairs⟩ := exists_saddle_selected_two_exterior_arcs
      psi hpsi u D R delta hR hd hdR hmorse hcoreBand N hN
      q hq hqpair gamma hgamma hgdis p hgend V hqlevel
      (by rw [hqlevel]; exact hnegative) (by rw [hqlevel]; exact hnegativeOpen)
  let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
    q (label k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
  have halpha (i : Fin 2) : Continuous (alpha i) ∧
      alpha i 0 = p (ends (i, 0)) ∧ alpha i 1 = p (ends (i, 1)) := by
    rcases harcs i with ⟨_, _, hs, _, _, h0, h1, _⟩
    exact ⟨hs.continuous, h0, h1⟩
  have hportLower (i k : Fin 2) : p (ep (i, k)) ∈ alpha i '' Icc (0 : ℝ) 1 := by
    have hm : ep (i, k) ∈ ({ep (i, 0), ep (i, 1)} : Set (Fin 4)) := by
      fin_cases k <;> simp
    rw [← hpairs i] at hm
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    rcases hm with hm | hm
    · exact ⟨0, by norm_num, (halpha i).2.1.trans (congrArg p hm).symm⟩
    · exact ⟨1, by norm_num, (halpha i).2.2.trans (congrArg p hm).symm⟩
  obtain ⟨F, K, Lbound, hK, hL, hF, hcF, Z, _hZ, _hFZ, _hZU,
    _hPhi, _hPhiInv, _hPhiFlow, _hPhiSupp, hSphere, _hFix, _hUnit,
    _hVo, _hDc, _hClosure, _hNative, _hWall, hTracks, hExterior⟩ :=
    exists_saddle_selected_wall_transport psi hpsi u D R delta hR hd hdR
      hmorse hcoreBand N hN
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => boundedFlowDiffeomorph F hK hL hF hcF t
  obtain ⟨ec, hec, hecs, _hect, _heci⟩ := exists_collar_chart psi hpsi
  have hej (x : UnitTwoSphere) : ec.symm (j x) = (x, 0) := by
    have hx : (x, (0 : ℝ)) ∈ ec.source := by
      rw [hecs]; exact ⟨mem_univ _, by norm_num⟩
    calc
      ec.symm (j x) = ec.symm (ec (x, 0)) := congrArg ec.symm (congrFun hec (x, 0)).symm
      _ = (x, 0) := ec.left_inv hx
  have hjtarget (x : UnitTwoSphere) : j x ∈ ec.target := by
    have hx : (x, (0 : ℝ)) ∈ ec.source := by
      rw [hecs]; exact ⟨mem_univ _, by norm_num⟩
    change psi (x, 0) ∈ ec.target
    rw [← congrFun hec (x, 0)]
    exact ec.map_source hx
  have hstay (x : UnitTwoSphere) : Phi (2 * delta) (j x) ∈ S := by
    have hglobal : Phi (2 * delta) '' S = S := (hSphere (2 * delta)).1
    rw [← hglobal]
    exact ⟨j x, ⟨x, rfl⟩, rfl⟩
  let G : UnitTwoSphere → UnitTwoSphere := fun x =>
    (ec.symm (Phi (2 * delta) (j x))).1
  have hG : Continuous G :=
    (continuous_fst.comp_continuousOn ec.symm.continuousOn).comp_continuous
      ((Phi (2 * delta)).continuous.comp hj.continuous) (fun x => by
        obtain ⟨y, hy⟩ := hstay x
        rw [← hy]
        exact hjtarget y)
  have hGrec (x : UnitTwoSphere) : j (G x) = Phi (2 * delta) (j x) := by
    obtain ⟨y, hy⟩ := hstay x
    change j ((ec.symm (Phi (2 * delta) (j x))).1) = _
    rw [← hy, hej y]
  have htime : delta - -delta = 2 * delta := by ring
  have hneg : |-delta| ≤ 2 * delta := by rw [abs_neg, abs_of_pos hd]; linarith
  have hpos : |delta| ≤ 2 * delta := by rw [abs_of_pos hd]; linarith
  have hport (i : Fin 4) : G (p i) = pplus i := by
    apply hji
    rw [hGrec]
    have hh := hTracks i 0 (by norm_num) (-delta) delta hneg hpos
    rw [htime] at hh
    simpa [p, pplus, m, pm, pp, aa, bb, rho, Phi, j, sx, sy, sub_eq_add_neg] using hh
  have helevels (t : ℝ) : (S ∩ {y : E3 | H y = c + t}) \ (j '' V) =
      j '' ({q : UnitTwoSphere | f q = c + t} \ V) := by
    ext y
    constructor
    · rintro ⟨⟨⟨x, rfl⟩, hx⟩, hn⟩
      exact ⟨x, ⟨hx, fun hVx => hn ⟨x, hVx, rfl⟩⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
      refine ⟨⟨⟨x, rfl⟩, hx⟩, ?_⟩
      rintro ⟨y, hy, hyx⟩
      exact hn (hji hyx ▸ hy)
  have hGlevel : G '' (Lm \ V) = Lp \ V := by
    apply hji.image_injective
    calc
      j '' (G '' (Lm \ V)) = Phi (2 * delta) '' (j '' (Lm \ V)) := by
        rw [image_image, image_image]
        exact image_congr (fun x _ => hGrec x)
      _ = j '' (Lp \ V) := by
        have hh := (hExterior (-delta) delta hneg hpos).1
        rw [htime] at hh
        change Phi (2 * delta) '' ((S ∩ {y : E3 | H y = c + -delta}) \ (j '' V)) =
          (S ∩ {y : E3 | H y = c + delta}) \ (j '' V) at hh
        rw [helevels (-delta), helevels delta] at hh
        have hc : c + -delta = c - delta := by ring
        simpa only [hc] using hh
  let E : Fin 2 → Set UnitTwoSphere := fun i => G '' (alpha i '' Icc (0 : ℝ) 1)
  let B : Fin 2 → Set UnitTwoSphere := fun i => range (beta i)
  have hEc (i : Fin 2) : IsConnected (E i) :=
    ((isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image (alpha i)
      (halpha i).1.continuousOn).image G hG.continuousOn
  have hBc (i : Fin 2) : IsConnected (B i) := isConnected_range (hbeta i)
  have hEend (i k : Fin 2) : pplus (ep (i, k)) ∈ E i := by
    exact ⟨p (ep (i, k)), hportLower i k, hport (ep (i, k))⟩
  have hB0 (i : Fin 2) : pplus (ep (i, 0)) ∈ B i := ⟨0, (hbend i).1⟩
  have hB1 (i : Fin 2) : pplus (ep (other i, 1)) ∈ B i := ⟨1, (hbend i).2⟩
  have h01 : (E 0 ∩ B 1).Nonempty := by
    refine ⟨pplus 1, ?_, ?_⟩
    · simpa [ep, finProdFinEquiv] using hEend 0 1
    · simpa [ep, other, finProdFinEquiv] using hB1 1
  have h12 : ((E 0 ∪ B 1) ∩ E 1).Nonempty := by
    refine ⟨pplus 2, Or.inr ?_, ?_⟩
    · simpa [ep, finProdFinEquiv] using hB0 1
    · simpa [ep, finProdFinEquiv] using hEend 1 0
  have h23 : (((E 0 ∪ B 1) ∪ E 1) ∩ B 0).Nonempty := by
    refine ⟨pplus 3, Or.inr ?_, ?_⟩
    · simpa [ep, finProdFinEquiv] using hEend 1 1
    · simpa [ep, other, finProdFinEquiv] using hB1 0
  have hconnected : IsConnected (((E 0 ∪ B 1) ∪ E 1) ∪ B 0) :=
    IsConnected.union h23 (IsConnected.union h12
      (IsConnected.union h01 (hEc 0) (hBc 1)) (hEc 1)) (hBc 0)
  have hEcover : (⋃ i : Fin 2, E i) = Lp \ V := by
    change (⋃ i : Fin 2, G '' (alpha i '' Icc (0 : ℝ) 1)) = _
    rw [← image_iUnion, ← hexterior]
    exact hGlevel
  have hcover : Lp = ((⋃ i : Fin 2, E i) ∪ ⋃ i : Fin 2, B i) := by
    rw [hEcover, ← hpositive]
    ext x
    constructor
    · intro hx
      by_cases hv : x ∈ V
      · exact Or.inr ⟨hx, hVD hv⟩
      · exact Or.inl ⟨hx, hv⟩
    · rintro (hx | hx) <;> exact hx.1
  have htwo (Z : Fin 2 → Set UnitTwoSphere) : (⋃ i : Fin 2, Z i) = Z 0 ∪ Z 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
  have hfinal : Lp = ((E 0 ∪ B 1) ∪ E 1) ∪ B 0 := by
    rw [hcover, htwo E, htwo B]
    ext x
    simp only [mem_union]
    tauto
  change IsConnected Lp
  rw [hfinal]
  exact hconnected

end PoincareConjecture.M25.Topology3D
