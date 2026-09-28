import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceOuterProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceUpperProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceLowerEndGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthCapEndTransport
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_reference_native_three_ends
    (ws wm d : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32)) :
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let S : Set E3 := (nestedReferenceBallChart d).boundary
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let mu : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    let alpha : ℝ := 17 / 16 + 1 / 131072
    let beta : ℝ := 17 / 16 + 1 / 65536
    ∃ (nu eta : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3),
      beta < k ∧ k < nu ∧ nu < mu ∧ 0 < eta ∧
      (∀ j : Fin 3,
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T j).source ∧
        ContDiffOn ℝ ∞ (T j) (T j).source ∧
        ContDiffOn ℝ ∞ (T j).symm (T j).target ∧
        (∀ p ∈ (T j).source, H0 (T j p) = p.2) ∧
        (∀ y ∈ (T j).target, ((T j).symm y).2 = H0 y)) ∧
      (∀ s ∈ Icc (alpha + d - eta) (beta + d + eta),
        S ∩ {y : E3 | H0 y = s} =
          T 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
            T 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
        T 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
          T 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ))) ∧
      (∀ s ∈ Icc (nu + d - eta) (nu + d + eta),
        T 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
          S ∩ {y : E3 | H0 y = s}) ∧
      ∀ P : SurgeryCapProfile, ∃ b0 : ℝ, 0 < b0 ∧
        ∀ lambda : Fin 3 → ℝ, (∀ j, 0 < lambda j) →
          (∀ j, lambda j * P.heightBound < b0) →
          let cut : Fin 3 → ℝ := ![beta + d, alpha + d, nu + d]
          let sign : Fin 3 → ℝ := ![1, 1, -1]
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let cap : Fin 3 → Set E3 := fun j =>
            P.capMap (T j) (cut j) (sign j) 0 (lambda j) '' Qminus
          let Lcyl : Set E3 := T 1 ''
            (sphere (0 : E2) 1 ×ˢ Icc (alpha + d) (beta + d))
          let M0 : Set E3 :=
            (S ∩ {y : E3 | beta + d ≤ H0 y ∧ H0 y ≤ nu + d}) ∪ Lcyl
          ∃ G0 : D3,
            G0 '' S = M0 ∪ ⋃ j : Fin 3, cap j ∧
            G0.symm '' (M0 ∪ ⋃ j : Fin 3, cap j) = S ∧
            (∀ y ∈ M0, G0 y = y ∧ G0.symm y = y) ∧
            (∀ (j : Fin 3) (y : E3), y ∈ cap j →
              |H0 y - cut j| ≤ lambda j * P.heightBound) := by
  classical
  let C := heightCoordinates
  let H0 : E3 → ℝ := fun y => (C y).2
  let S := (nestedReferenceBallChart d).boundary
  let U : E2 → ℝ := fun x => ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
  let k := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
  let mu := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
  let alpha : ℝ := 17 / 16 + 1 / 131072
  let beta : ℝ := 17 / 16 + 1 / 65536
  change ∃ (nu eta : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3),
    beta < k ∧ k < nu ∧ nu < mu ∧ _
  obtain ⟨ws0, wm0, hwslo0, hwshi0, hwsroot0, hwmlo0, hwmhi0, hwmroot0, hUp⟩ :=
    exists_upper_reference_profile_ball_family
  obtain ⟨w, _, hwunique⟩ := exists_unique_nestedReference_saddle_root
  have hseq : ws0 = ws := (hwunique ws0 ⟨hwslo0, hwshi0, hwsroot0⟩).trans
    (hwunique ws ⟨hwslo, hwshi, hwsroot⟩).symm
  subst ws0
  let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
  have hgder (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) (1 / 2)) :
      HasDerivAt g ((1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2))) w ∧
        0 < (1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2)) := by
    have hrad0 : 0 < 1 - w ^ 2 := by nlinarith only [hw.1, hw.2]
    have hcube := pow_le_pow_left₀ hw.1.le hw.2.le 3
    norm_num at hcube
    let r : ℝ := Real.sqrt (1 - w ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.mpr hrad0
    have hr2 : r ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hrad0.le
    have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / w ^ 2) w :=
      (hasDerivAt_id w).inv hw.1.ne'
    have ha : HasDerivAt (fun x : ℝ => 2 - 1 / x) (1 / w ^ 2) w := by
      simpa only [one_div, neg_div, neg_neg] using hinv.const_sub (2 : ℝ)
    have hradder : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * w) w := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one, neg_mul] using ((hasDerivAt_id w).pow 2).const_sub (1 : ℝ)
    have hh : HasDerivAt g
        ((1 / w ^ 2) * r + (2 - 1 / w) * ((-2 * w) / (2 * r))) w :=
      ha.mul (hradder.sqrt hrad0.ne')
    have halg : (1 / w ^ 2) * r + (2 - 1 / w) * ((-2 * w) / (2 * r)) =
        (1 - 2 * w ^ 3) / (w ^ 2 * r) := by
      calc
        _ = r ^ 2 / (w ^ 2 * r) + (w ^ 2 - 2 * w ^ 3) / (w ^ 2 * r) := by
          congr 1
          · field_simp [hw.1.ne', hr0.ne']
          · field_simp [hw.1.ne', hr0.ne']
            ring
        _ = (1 - 2 * w ^ 3) / (w ^ 2 * r) := by
          rw [← add_div]
          congr 1
          nlinarith only [hr2]
    rw [halg] at hh
    exact ⟨hh, div_pos (by linarith only [hcube]) (mul_pos (sq_pos_of_pos hw.1) hr0)⟩
  have hgmono : StrictMonoOn g (Ioo (0 : ℝ) (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun w hw => (hgder w hw).1.continuousAt.continuousWithinAt)
    intro w hw
    obtain ⟨hd, hp⟩ := hgder w (interior_subset hw)
    rw [hd.deriv]
    exact hp
  have hmeq : wm0 = wm := hgmono.injOn ⟨hwmlo0, hwmhi0⟩ ⟨hwmlo, hwmhi⟩
    (hwmroot0.trans hwmroot.symm)
  subst wm0
  obtain ⟨rhoU, eu0, eu, cu, _, _, hklo, _, _, _, _, hrho, hsep,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTubesU⟩ := hUp
  have hksq : ‖(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)‖ ^ 2 = 1 - ws ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using
      Real.sq_sqrt (show 0 ≤ 1 - ws ^ 2 by nlinarith only [hwslo, hwshi])
  have hmsq : ‖(!₂[Real.sqrt (1 - wm ^ 2), 0] : E2)‖ ^ 2 = 1 - wm ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using
      Real.sq_sqrt (show 0 ≤ 1 - wm ^ 2 by nlinarith only [hwmlo, hwmhi])
  have hUk : U !₂[-Real.sqrt (1 - ws ^ 2), 0] = k := by
    change ‖(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)‖ ^ 2 +
      Real.sqrt (1 - ‖(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)‖ ^ 2) +
      -Real.sqrt (1 - ws ^ 2) / 32 = k
    rw [hksq, show 1 - (1 - ws ^ 2) = ws ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos (by linarith only [hwslo])]
    dsimp only [k]
    ring
  have hUm : U !₂[Real.sqrt (1 - wm ^ 2), 0] = mu := by
    change ‖(!₂[Real.sqrt (1 - wm ^ 2), 0] : E2)‖ ^ 2 +
      Real.sqrt (1 - ‖(!₂[Real.sqrt (1 - wm ^ 2), 0] : E2)‖ ^ 2) +
      Real.sqrt (1 - wm ^ 2) / 32 = mu
    rw [hmsq, show 1 - (1 - wm ^ 2) = wm ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos hwmlo]
  change 37 / 32 < U !₂[-Real.sqrt (1 - ws ^ 2), 0] at hklo
  change U !₂[-Real.sqrt (1 - ws ^ 2), 0] <
    U !₂[Real.sqrt (1 - wm ^ 2), 0] - 9 * rhoU ^ 2 at hsep
  rw [hUk] at hklo
  rw [hUk, hUm] at hsep
  let nu := mu - rhoU ^ 2
  let deltaU := rhoU ^ 2 / 8
  have hrho2 : 0 < rhoU ^ 2 := sq_pos_of_pos hrho
  have hdeltaU : 0 < deltaU := by dsimp only [deltaU]; positivity
  have hknu : k < nu := by dsimp only [nu]; linarith only [hsep, hrho2]
  have hnumu : nu < mu := by dsimp only [nu]; linarith only [hrho2]
  have hbetak : beta < k := by dsimp only [beta]; linarith only [hklo]
  obtain ⟨Tu, _, _, _, _, _, _, hTu, hTui, hTus, hTuh, hTuhi, hUcuts, hUcaps⟩ :=
    hTubesU d
  dsimp only [U] at hUm
  dsimp only at hUcuts hUcaps
  rw [hUm] at hUcuts hUcaps
  obtain ⟨vmin, mi, ei, ki, _, _, _, _, _, _, _, _, _, _, _, _, _, hTubesI⟩ :=
    exists_inner_reference_profile_ball_family
  obtain ⟨Ti, _, _, _, _, _, hTitarget, hTi, hTii, hTis, hTih, hTihi,
    hIcuts, _, hIcaps⟩ := hTubesI d
  obtain ⟨rho, _, hroot, F, _, _, _, _, himages, hTubesO⟩ :=
    exists_outer_reference_profile_ball_family
  obtain ⟨To, hTo, hToi, hOcaps⟩ := hTubesO d
  have hToh (p : E2 × ℝ) : H0 (To p) = p.2 := by
    dsimp only [H0, C]
    rw [hTo, heightCoordinates.apply_symm_apply]
  have hTohi (y : E3) : (To.symm y).2 = H0 y := by rw [hToi]
  let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
  let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
  let Ei : ℝ → Set E3 := fun h =>
    (fun x : E2 => C.symm (x, U x + d)) '' {x | ‖x‖ < 1 / 2 ∧ U x ≤ h}
  let Eo : ℝ → Set E3 := fun h => j '' {q : UnitTwoSphere |
    (C (q : E3)).2 ≤ 0 ∨ rho ((C (q : E3)).1 0 / ‖(C (q : E3)).1‖, h) ≤
      ‖(C (q : E3)).1‖}
  let O : Set E3 := j '' {q : UnitTwoSphere |
    (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖}
  have hSrange : range j = S := by
    ext y
    change (∃ q : UnitTwoSphere, j q = y) ↔
      ∃ x ∈ sphere (0 : E3) 1, nestedReferenceDiffeomorph d x = y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, hxy⟩
  have hgeom := reference_lower_end_geometry rho F d To hTo
    (fun theta ht h hh => by
      have hp := hroot (theta, h) ⟨ht, ⟨by linarith only [hh.1],
        by linarith only [hh.2]⟩⟩
      exact ⟨hp.1, hp.2.1, hp.2.2.1⟩) himages
  change (∀ h ∈ J, IsCompact (Ei h) ∧ IsCompact (Eo h) ∧ Eo h ⊆ O ∧
    range j ∩ {y : E3 | H0 y ≤ h + d} = Ei h ∪ Eo h ∧ _) ∧ _ at hgeom
  rw [hSrange] at hgeom
  let eta := min (1 / 262144 : ℝ) (deltaU / 4)
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hdeltaU (by norm_num))
  have hetaL : eta ≤ 1 / 262144 := min_le_left _ _
  have hetaU : eta ≤ deltaU / 4 := min_le_right _ _
  have hlowwin (s : ℝ) (hs : s ∈ Icc (alpha + d - eta) (beta + d + eta)) :
      s - d ∈ J ∧ s - d ∈ Icc (17 / 16 - (1 / 8192) / 2 : ℝ)
        (17 / 16 + (1 / 8192) / 2) := by
    dsimp only [alpha, beta] at hs
    constructor <;> constructor <;>
      linarith only [hs.1, hs.2, hetaL]
  have hlower (s : ℝ) (hs : s ∈ Icc (alpha + d - eta) (beta + d + eta)) :
      S ∩ {y : E3 | H0 y = s} =
        Ti '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
          To '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
      Ti '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        To '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    obtain ⟨hc, _, hsph⟩ := hIcuts s (hlowwin s hs).2
    have hh (x : E2) (hx : x ∈ closedBall (0 : E2) (1 / 2) ∧ U x ≤ s - d) :
        ‖x‖ < 1 / 2 := by
      have hxIm : C.symm (x, s) ∈ Ti '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
        rw [hc]
        exact ⟨(x, s), ⟨hx, rfl⟩, rfl⟩
      obtain ⟨p, hp, hpx⟩ := hxIm
      have hm := Ti.map_source (hTis ⟨hp.1, mem_univ _⟩)
      rw [hpx, hTitarget] at hm
      change ‖(C (C.symm (x, s))).1‖ < 1 / 2 ∧ _ at hm
      simpa only [C.apply_symm_apply] using hm.1
    have heq : {x : E2 | x ∈ closedBall 0 (1 / 2) ∧ U x ≤ s - d} =
        {x | ‖x‖ < 1 / 2 ∧ U x ≤ s - d} := by
      ext x
      exact ⟨fun hx => ⟨hh x hx, hx.2⟩,
        fun hx => ⟨mem_closedBall_zero_iff.mpr hx.1.le, hx.2⟩⟩
    have heqs : {x : E2 | x ∈ closedBall 0 (1 / 2) ∧ U x = s - d} =
        {x | ‖x‖ < 1 / 2 ∧ U x = s - d} := by
      ext x
      exact ⟨fun hx => ⟨hh x ⟨hx.1, hx.2.le⟩, hx.2⟩,
        fun hx => ⟨mem_closedBall_zero_iff.mpr hx.1.le, hx.2⟩⟩
    rw [heq] at hc
    rw [heqs] at hsph
    have hg := hgeom.1 (s - d) (hlowwin s hs).1
    rw [hc, hsph]
    simpa only [sub_add_cancel] using hg.2.2.2.2
  let T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3 :=
    ![Ti, To.toHomeomorph.toOpenPartialHomeomorph, Tu]
  have hTd (j : Fin 3) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T j).source ∧
      ContDiffOn ℝ ∞ (T j) (T j).source ∧
      ContDiffOn ℝ ∞ (T j).symm (T j).target ∧
      (∀ p ∈ (T j).source, H0 (T j p) = p.2) ∧
      (∀ y ∈ (T j).target, ((T j).symm y).2 = H0 y) := by
    fin_cases j
    · exact ⟨hTis, hTi, hTii, fun p _ => hTih p, fun y _ => hTihi y⟩
    · exact ⟨subset_univ _, To.contDiff.contDiffOn, To.symm.contDiff.contDiffOn,
        fun p _ => hToh p, fun y _ => hTohi y⟩
    · exact ⟨hTus, hTu, hTui, fun p _ => hTuh p, fun y _ => hTuhi y⟩
  refine ⟨nu, eta, T, hbetak, hknu, hnumu, heta, hTd, hlower, ?_, ?_⟩
  · intro s hs
    have hw : s - d ∈ Icc (nu - deltaU / 2) (nu + deltaU / 2) :=
      ⟨by linarith only [hs.1, hetaU, hdeltaU],
        by linarith only [hs.2, hetaU, hdeltaU]⟩
    exact (hUcuts s hw).2.2.2
  intro P
  obtain ⟨B0, hB0, hOprofile⟩ := hOcaps P
  let AP := 1 + B0 + P.heightBound
  have hAP : 0 < AP := by dsimp only [AP]; linarith only [hB0, P.one_le_heightBound]
  let b0 : ℝ := min (1 / 2) (min ((1 / 8192) / 32)
    (min (deltaU / 32) (min ((beta - alpha) / 8)
      (min ((nu - beta) / 8) ((1 / 131072) / (2 * AP))))))
  have hab : alpha < beta := by norm_num [alpha, beta]
  have hbnu : beta < nu := hbetak.trans hknu
  have hb0 : 0 < b0 := by
    dsimp only [b0]
    refine lt_min (by norm_num) (lt_min (by norm_num)
      (lt_min (div_pos hdeltaU (by norm_num))
        (lt_min (div_pos (sub_pos.mpr hab) (by norm_num))
          (lt_min (div_pos (sub_pos.mpr hbnu) (by norm_num)) ?_))))
    exact div_pos (by norm_num) (mul_pos (by norm_num) hAP)
  have hb : b0 ≤ 1 / 2 ∧ b0 ≤ (1 / 8192) / 32 ∧ b0 ≤ deltaU / 32 ∧
      b0 ≤ (beta - alpha) / 8 ∧ b0 ≤ (nu - beta) / 8 ∧
      b0 ≤ (1 / 131072) / (2 * AP) := by
    have hb' : b0 ≤ min (1 / 2) (min ((1 / 8192) / 32)
        (min (deltaU / 32) (min ((beta - alpha) / 8)
          (min ((nu - beta) / 8) ((1 / 131072) / (2 * AP)))))) := le_rfl
    simpa only [le_min_iff] using hb'
  refine ⟨b0, hb0, ?_⟩
  intro lambda hlambda hsmall
  let cut : Fin 3 → ℝ := ![beta + d, alpha + d, nu + d]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  let Qminus := {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0}
  let Qplus := {q : UnitTwoSphere | 0 ≤ (C (q : E3)).2}
  let cap : Fin 3 → Set E3 := fun j =>
    P.capMap (T j) (cut j) (sign j) 0 (lambda j) '' Qminus
  let Lcyl : Set E3 := To '' (sphere (0 : E2) 1 ×ˢ Icc (alpha + d) (beta + d))
  let Rbeta : Set E3 := S ∩ {y : E3 | beta + d ≤ H0 y}
  let Rnu : Set E3 := S ∩ {y : E3 | H0 y ≤ nu + d}
  let Eu : Set E3 := S ∩ {y : E3 | nu + d ≤ H0 y}
  let Bmid : Set E3 := S ∩ {y : E3 | beta + d ≤ H0 y ∧ H0 y ≤ nu + d}
  let M0 := Bmid ∪ Lcyl
  change ∃ G0 : D3, G0 '' S = M0 ∪ ⋃ j : Fin 3, cap j ∧ _
  have hcapheight (j : Fin 3) (y : E3) (hy : y ∈ cap j) :
      |H0 y - cut j| ≤ lambda j * P.heightBound := by
    obtain ⟨q, _, rfl⟩ := hy
    rw [SurgeryCapProfile.capMap_apply, (hTd j).2.2.2.1 _
      ((hTd j).1 ⟨by simpa only [mem_closedBall, dist_zero_right]
        using P.model_fst_norm_le q, mem_univ _⟩)]
    have hsign : |sign j| = 1 := by fin_cases j <;> norm_num [sign]
    simp only [add_sub_cancel_left, zero_add, abs_mul, hsign, one_mul,
      abs_of_pos (hlambda j)]
    exact mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda j).le
  have hcapClosed (j : Fin 3) : IsClosed (cap j) :=
    (((isClosed_le (C.continuous.comp continuous_subtype_val).snd
      continuous_const).isCompact).image
        (P.capMap_contMDiff (T j) (hTd j).1 (hTd j).2.1
          (cut j) (sign j) 0 (lambda j)).continuous).isClosed
  have hSclosed : IsClosed S := by
    change IsClosed (nestedReferenceBallChart d).boundary
    rw [← (nestedReferenceBallChart d).frontier_inside]
    exact isClosed_frontier
  have hHc : Continuous H0 := C.continuous.snd
  have hRb : IsClosed Rbeta := hSclosed.inter (isClosed_le continuous_const hHc)
  have hRn : IsClosed Rnu := hSclosed.inter (isClosed_le hHc continuous_const)
  have hLc : IsCompact Lcyl := ((isCompact_sphere (0 : E2) 1).prod isCompact_Icc).image
    To.continuous
  have hLheight (y : E3) (hy : y ∈ Lcyl) : H0 y ∈ Icc (alpha + d) (beta + d) := by
    obtain ⟨p, hp, rfl⟩ := hy
    simpa only [hToh] using hp.2
  have halpha : alpha ∈ J := by norm_num [alpha, J]
  have hbeta : beta ∈ J := by norm_num [beta, J]
  have hEoc : IsCompact (Eo beta) := (hgeom.1 beta hbeta).2.1
  have hEoO : Eo beta ⊆ O := (hgeom.1 beta hbeta).2.2.1
  have hEoL : Eo beta = Eo alpha ∪ Lcyl := (hgeom.2 alpha beta halpha hbeta hab.le).1
  have hLsub : Lcyl ⊆ Eo beta := by rw [hEoL]; exact subset_union_right
  have hOsub : Eo alpha ⊆ Eo beta := by rw [hEoL]; exact subset_union_left
  have hsplit : S = (Ei beta ∪ Eo alpha) ∪ Lcyl ∪ Rbeta := by
    have hg := (hgeom.1 beta hbeta).2.2.2.1
    rw [hEoL] at hg
    ext y
    constructor
    · intro hy
      by_cases hh : H0 y ≤ beta + d
      · have hmem := hg.subset ⟨hy, hh⟩
        rcases hmem with hi | ho | hc
        · exact Or.inl (Or.inl (Or.inl hi))
        · exact Or.inl (Or.inl (Or.inr ho))
        · exact Or.inl (Or.inr hc)
      · exact Or.inr ⟨hy, (lt_of_not_ge hh).le⟩
    · rintro (((hi | ho) | hc) | hr)
      · exact (hg.superset (Or.inl hi)).1
      · exact (hg.superset (Or.inr (Or.inl ho))).1
      · exact (hg.superset (Or.inr (Or.inr hc))).1
      · exact hr.1
  have herr (j : Fin 3) : 0 < lambda j * P.heightBound :=
    mul_pos (hlambda j) (lt_of_lt_of_le zero_lt_one P.one_le_heightBound)
  have hlle (j : Fin 3) : lambda j ≤ lambda j * P.heightBound := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left P.one_le_heightBound (hlambda j).le
  have hsepIO : lambda 0 * P.heightBound + lambda 1 * P.heightBound < beta - alpha := by
    calc
      _ < b0 + b0 := add_lt_add (hsmall 0) (hsmall 1)
      _ < 8 * b0 := by linarith only [hb0]
      _ ≤ beta - alpha := by
        simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hb.2.2.2.1
  have hsepIU : lambda 0 * P.heightBound + lambda 2 * P.heightBound < nu - beta := by
    calc
      _ < b0 + b0 := add_lt_add (hsmall 0) (hsmall 2)
      _ < 8 * b0 := by linarith only [hb0]
      _ ≤ nu - beta := by
        simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hb.2.2.2.2.1
  have hsepOU : lambda 1 * P.heightBound + lambda 2 * P.heightBound < nu - beta := by
    calc
      _ < b0 + b0 := add_lt_add (hsmall 1) (hsmall 2)
      _ < 8 * b0 := by linarith only [hb0]
      _ ≤ nu - beta := by
        simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hb.2.2.2.2.1
  have hshortI : lambda 0 * P.heightBound < min ((1 / 8192) / 16 : ℝ) 1 :=
    lt_min (by linarith only [hsmall 0, hb.2.1]) (by linarith only [hsmall 0, hb.1])
  have hshortU : lambda 2 * P.heightBound < min (deltaU / 16) 1 :=
    lt_min (by linarith only [hsmall 2, hb.2.2.1, hdeltaU])
      (by linarith only [hsmall 2, hb.1])
  have hshortO : lambda 1 * (1 + B0 + P.heightBound) < min (1 / 131072 : ℝ) 1 := by
    have hbound := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hAP)).mp hb.2.2.2.2.2
    have hmul := mul_lt_mul_of_pos_right ((hlle 1).trans_lt (hsmall 1)) hAP
    change lambda 1 * AP < _
    norm_num
    nlinarith only [hbound, hmul]
  let ci : UnitTwoSphere → E3 := fun q => Ti ((P.model q).1, beta + d + lambda 0 * (P.model q).2)
  let co : UnitTwoSphere → E3 := fun q => To ((P.model q).1, alpha + d + lambda 1 * (P.model q).2)
  let cu' : UnitTwoSphere → E3 := fun q => Tu ((P.model q).1, nu + d - lambda 2 * (P.model q).2)
  let ni := ci '' Qplus
  let no := co '' Qplus
  let northU := cu' '' Qplus
  have hcapI : cap 0 = ci '' Qminus := by
    change P.capMap Ti (beta + d) 1 0 (lambda 0) '' Qminus = _
    congr 1
    funext q
    simp only [SurgeryCapProfile.capMap_apply, zero_add, one_mul, ci]
  have hcapO : cap 1 = co '' Qminus := by
    change P.capMap To.toHomeomorph.toOpenPartialHomeomorph (alpha + d) 1 0 (lambda 1) '' Qminus = _
    congr 1
    funext q
    simp only [SurgeryCapProfile.capMap_apply, zero_add, one_mul, co]
    rfl
  have hcapU : cap 2 = cu' '' Qminus := by
    change P.capMap Tu (nu + d) (-1) 0 (lambda 2) '' Qminus = _
    congr 1
    funext q
    simp only [SurgeryCapProfile.capMap_apply, zero_add, neg_one_mul, sub_eq_add_neg, cu']
  have hIP := hIcaps P beta 1 (lambda 0) (by norm_num [beta]) (by norm_num) (hlambda 0) hshortI
  obtain ⟨Ji, gi, ai, Ai, _hJi, _hgif, _hgi, _hgim, _hgi0, _hgia,
    _hai, _haip, _hain, _hais, _hAis, _hAit, _hAif, _hAii, _hEi, _hSi,
    hAib, hAir, _hAicuts, _hAiheight, _hAiinside, _hAipatch, _hAiS, _hAiO, hAiavoid,
    Ni, hNib, _hNis, _hNit, _hNif, _hNii, hNic, _hNishort, hNin, hNir, hNip⟩ := hIP
  change Ai.boundary = Ei beta ∪ ni at hAib
  change Ei beta ∩ ni = _ at hAir
  change Ni.boundary = ci '' Qminus ∪ ni at hNib
  change ni = Ni.chart '' _ at hNin
  change ci '' Qminus ∩ ni = _ at hNir
  change Ai.closedRegion ∩ ((range j ∩ {y : E3 | beta + d ≤ H0 y}) ∪ O) ⊆ ni at hAiavoid
  rw [hSrange] at hAiavoid
  have move (A N : BallNeighborhoodChart E3 E3) (E B D R K : Set E3)
      (hAb : A.boundary = E ∪ D) (hNb : N.boundary = B ∪ D)
      (hEr : E ∩ D = R) (hBr : B ∩ D = R)
      (hDn : D = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (C y).2})
      (hNc : N.closedRegion ⊆ A.closedRegion)
      (hp : ∀ q : UnitTwoSphere, -1 / 8 < (C (q : E3)).2 → N.chart (q : E3) ∈ A.boundary)
      (hK : IsClosed K) (hav : A.closedRegion ∩ K ⊆ D) :
      ∃ G : D3, G '' E = B ∧ G.symm '' B = E ∧
        ∀ y ∈ K, G y = y ∧ G.symm y = y := by
    change D = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} at hDn
    rw [hDn] at hAb hNb hEr hBr hav
    obtain ⟨G, _, hG, hGi, hf, _, _, _, _⟩ :=
      exists_saddle_north_cap_end_transport A N (1 / 8) (by norm_num) (by norm_num)
        (by simpa only [C, neg_div] using hp) hNc E B K hK hAb hNb
        (hEr.trans hBr.symm) hav
    exact ⟨G, hG, hGi, fun y hy => hf y (Or.inr hy)⟩
  obtain ⟨Gi, hGi, _, hGifix⟩ := move Ai Ni (Ei beta) (ci '' Qminus) ni _
    (Rbeta ∪ Eo beta) hAib hNib hAir hNir hNin hNic hNip (hRb.union hEoc.isClosed)
    (by
      rintro y ⟨hyA, hyR | hyO⟩
      · exact hAiavoid ⟨hyA, Or.inl hyR⟩
      · exact hAiavoid ⟨hyA, Or.inr (hEoO hyO)⟩)
  rw [← hcapI] at hGi
  obtain ⟨phiO, hOP⟩ := hOprofile alpha 1 (lambda 1) (by norm_num [alpha])
    (by norm_num) (hlambda 1) hshortO
  let Ao := (nestedReferenceBallChart d).mapDiffeomorph phiO
  obtain ⟨_hAos, _hAot, _hAof, _hAoi, _hEo, _hOfix, hAob, hAor, _hAocuts,
    hAoheight, _hAocyl, hAoavoid, _hAosolid, No, _hNos, _hNot, _hNof, _hNoi,
    hNob, hNoc, _hNoshort, hNon, hNor, hNop⟩ := hOP
  change Ao.boundary = Eo alpha ∪ no at hAob
  change Eo alpha ∩ no = _ at hAor
  change No.boundary = co '' Qminus ∪ no at hNob
  change no = No.chart '' _ at hNon
  change co '' Qminus ∩ no = _ at hNor
  have hOavoid : Ao.closedRegion ∩ ((Rbeta ∪ Lcyl) ∪ cap 0) ⊆ no := by
    rintro y ⟨hyA, (hyR | hyL) | hyI⟩
    · have hh := (hAoheight y hyA).2
      have hy : beta + d ≤ H0 y := hyR.2
      have hp := herr 0
      change H0 y ≤ alpha + d + lambda 1 * P.heightBound at hh
      exfalso
      linarith only [hh, hy, hsepIO, hp]
    · exact hAoavoid ⟨hyA, by
        obtain ⟨p, hp, rfl⟩ := hyL
        exact ⟨p, ⟨hp.1, hp.2.1⟩, rfl⟩⟩
    · have hh := (hAoheight y hyA).2
      have hy := (abs_le.mp (hcapheight 0 y hyI)).1
      change -(lambda 0 * P.heightBound) ≤ H0 y - (beta + d) at hy
      change H0 y ≤ alpha + d + lambda 1 * P.heightBound at hh
      exfalso
      linarith only [hh, hy, hsepIO]
  obtain ⟨Go, hGo, _, hGofix⟩ := move Ao No (Eo alpha) (co '' Qminus) no _
    ((Rbeta ∪ Lcyl) ∪ cap 0) hAob hNob hAor hNor hNon hNoc hNop
      ((hRb.union hLc.isClosed).union (hcapClosed 0)) hOavoid
  rw [← hcapO] at hGo
  have hnuWin : nu ∈ Icc (nu - deltaU / 4) (nu + deltaU / 4) :=
    ⟨sub_le_self _ (div_nonneg hdeltaU.le (by norm_num)),
      le_add_of_nonneg_right (div_nonneg hdeltaU.le (by norm_num))⟩
  have hUP := hUcaps P nu 1 (lambda 2) hnuWin (by norm_num) (hlambda 2) hshortU
  obtain ⟨Ju, gu, au, Au, _hJu, _hguf, _hgu, _hgum, _hgu0, _hgua,
    _hau, _haup, _haun, _haus, _hAus, _hAut, _hAuf, _hAui, _hSu, hAub, hAur,
    _hAucuts, hAuheight, _hAuinside, _hAuclosed, _hAuin, _hAupatch, _hAuS,
    hAuavoid, _hAufar, Nu, hNub, _hNus, _hNut, _hNuf, _hNui, hNuc, _hNushort,
    hNun, hNur, hNup⟩ := hUP
  change Au.boundary = Eu ∪ northU at hAub
  change Eu ∩ northU = _ at hAur
  change Nu.boundary = cu' '' Qminus ∪ northU at hNub
  change northU = Nu.chart '' _ at hNun
  change cu' '' Qminus ∩ northU = _ at hNur
  change Au.closedRegion ∩ Rnu ⊆ northU at hAuavoid
  have hUavoid : Au.closedRegion ∩ (((Rnu ∪ Lcyl) ∪ cap 0) ∪ cap 1) ⊆ northU := by
    rintro y ⟨hyA, ((hyR | hyL) | hyI) | hyO⟩
    · exact hAuavoid ⟨hyA, hyR⟩
    · have hh := (hAuheight y hyA).2.1
      have hy := (hLheight y hyL).2
      have hp := herr 0
      change nu + d - lambda 2 * P.heightBound ≤ H0 y at hh
      exfalso
      linarith only [hh, hy, hsepIU, hp]
    · have hh := (hAuheight y hyA).2.1
      have hy := (abs_le.mp (hcapheight 0 y hyI)).2
      change H0 y - (beta + d) ≤ lambda 0 * P.heightBound at hy
      change nu + d - lambda 2 * P.heightBound ≤ H0 y at hh
      exfalso
      linarith only [hh, hy, hsepIU]
    · have hh := (hAuheight y hyA).2.1
      have hy := (abs_le.mp (hcapheight 1 y hyO)).2
      change H0 y - (alpha + d) ≤ lambda 1 * P.heightBound at hy
      change nu + d - lambda 2 * P.heightBound ≤ H0 y at hh
      exfalso
      linarith only [hh, hy, hsepOU, hab]
  obtain ⟨Gu, hGu, _, hGufix⟩ := move Au Nu Eu (cu' '' Qminus) northU _
    (((Rnu ∪ Lcyl) ∪ cap 0) ∪ cap 1) hAub hNub hAur hNur hNun hNuc hNup
    (((hRn.union hLc.isClosed).union (hcapClosed 0)).union (hcapClosed 1)) hUavoid
  rw [← hcapU] at hGu
  have hRsplit : Rbeta = Bmid ∪ Eu := by
    ext y
    constructor
    · intro hy
      by_cases hh : H0 y ≤ nu + d
      · exact Or.inl ⟨hy.1, hy.2, hh⟩
      · exact Or.inr ⟨hy.1, (lt_of_not_ge hh).le⟩
    · rintro (hy | hy)
      · exact ⟨hy.1, hy.2.1⟩
      · have hh : nu + d ≤ H0 y := hy.2
        exact ⟨hy.1, by change beta + d ≤ H0 y; linarith only [hh, hbnu]⟩
  have fixedImage (G : D3) (B : Set E3) (hf : ∀ y ∈ B, G y = y) : G '' B = B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hf x hx] using hx
    · intro hy
      exact ⟨y, hy, hf y hy⟩
  have hGiR := fixedImage Gi Rbeta (fun y hy => (hGifix y (Or.inl hy)).1)
  have hGiO := fixedImage Gi (Eo alpha) (fun y hy => (hGifix y (Or.inr (hOsub hy))).1)
  have hGiL := fixedImage Gi Lcyl (fun y hy => (hGifix y (Or.inr (hLsub hy))).1)
  have hGoR := fixedImage Go Rbeta (fun y hy => (hGofix y (Or.inl (Or.inl hy))).1)
  have hGoL := fixedImage Go Lcyl (fun y hy => (hGofix y (Or.inl (Or.inr hy))).1)
  have hGoI := fixedImage Go (cap 0) (fun y hy => (hGofix y (Or.inr hy)).1)
  have hGuR := fixedImage Gu Bmid (fun y hy =>
    (hGufix y (Or.inl (Or.inl (Or.inl ⟨hy.1, hy.2.2⟩)))).1)
  have hGuL := fixedImage Gu Lcyl (fun y hy => (hGufix y (Or.inl (Or.inl (Or.inr hy)))).1)
  have hGuI := fixedImage Gu (cap 0) (fun y hy => (hGufix y (Or.inl (Or.inr hy))).1)
  have hGuO := fixedImage Gu (cap 1) (fun y hy => (hGufix y (Or.inr hy)).1)
  have hUnion : (⋃ j : Fin 3, cap j) = (cap 0 ∪ cap 1) ∪ cap 2 := by
    ext y
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨j, hj⟩
      fin_cases j
      · exact Or.inl (Or.inl hj)
      · exact Or.inl (Or.inr hj)
      · exact Or.inr hj
    · rintro ((hi | ho) | hu)
      · exact ⟨0, hi⟩
      · exact ⟨1, ho⟩
      · exact ⟨2, hu⟩
  let G0 := (Gi.trans Go).trans Gu
  have hGiS : Gi '' S = cap 0 ∪ Eo alpha ∪ Lcyl ∪ Rbeta := by
    rw [hsplit]
    simp only [image_union, hGi, hGiO, hGiL, hGiR]
  have hGoS : Go '' (cap 0 ∪ Eo alpha ∪ Lcyl ∪ Rbeta) =
      cap 0 ∪ cap 1 ∪ Lcyl ∪ Rbeta := by
    simp only [image_union, hGoI, hGo, hGoL, hGoR]
  have hG0 : G0 '' S = M0 ∪ ⋃ j : Fin 3, cap j := by
    change (Gu ∘ (Go ∘ Gi)) '' S = _
    rw [image_comp, image_comp, hGiS, hGoS, hRsplit]
    simp only [image_union, hGuI, hGuO, hGuL, hGuR, hGu, hUnion]
    dsimp only [M0]
    ext y
    simp only [mem_union]
    tauto
  refine ⟨G0, hG0, ?_, ?_, hcapheight⟩
  · change G0.symm '' (M0 ∪ ⋃ j : Fin 3, cap j) = S
    rw [← hG0]
    exact G0.symm_image_image S
  · intro y hy
    have hi := hGifix y (hy.elim (fun hy => Or.inl ⟨hy.1, hy.2.1⟩)
      (fun hy => Or.inr (hLsub hy)))
    have ho := hGofix y (Or.inl (hy.elim
      (fun hy => Or.inl ⟨hy.1, hy.2.1⟩) Or.inr))
    have hu := hGufix y (Or.inl (Or.inl
      (hy.elim (fun hy => Or.inl ⟨hy.1, hy.2.2⟩) Or.inr)))
    constructor
    · change Gu (Go (Gi y)) = y
      rw [hi.1, ho.1, hu.1]
    · change Gi.symm (Go.symm (Gu.symm y)) = y
      rw [hu.2, ho.2, hi.2]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
