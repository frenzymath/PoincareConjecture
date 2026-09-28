import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsLevels
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import PoincareConjecture.Proofs.M25.Mathlib.ClosedPrefixTrap
import Mathlib.Analysis.Calculus.Deriv.MeanValue











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D



theorem FamilyCutState.retainedCore_of_affine_height_path
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (z0 : ℝ)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal < z0)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      z0 < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (gamma : ℝ → E3) (T : ℝ)
    (hT : T ∈ uIcc 0 (z0 - ⟪(u : E3), gamma 0⟫_ℝ))
    (hcont : ContinuousOn gamma (uIcc 0 T))
    (hsphere : ∀ t ∈ uIcc 0 T,
      gamma t ∈ range (fun q : UnitTwoSphere => psi i (q, 0)))
    (hstart : gamma 0 ∈ S.retainedCore i)
    (hheight : ∀ t ∈ uIcc 0 T,
      ⟪(u : E3), gamma t⟫_ℝ = ⟪(u : E3), gamma 0⟫_ℝ + t) :
    ∀ t ∈ uIcc 0 T, gamma t ∈ S.retainedCore i := by
  classical
  obtain ⟨hK, _hconn, _hdef, hcover, hinter⟩ := S.retainedCore_geometry i
  intro t ht
  by_cases ht0 : t = 0
  · simpa only [ht0] using hstart
  by_contra hout
  have hcap : gamma t ∈
      ⋃ a : {a : Fin S.capCount // S.owner a = i}, (S.cap a.1).cap := by
    have hmem := hsphere t ht
    rw [hcover] at hmem
    exact hmem.resolve_left hout
  obtain ⟨a, ha⟩ := mem_iUnion.mp hcap
  have hnotseam : gamma t ∉ (S.cap a.1).seam := by
    intro h
    exact hout ((hinter a.1 a.2 ▸ h : gamma t ∈
      S.retainedCore i ∩ (S.cap a.1).cap).1)
  have hstrict := ((S.cap a.1).cap_seam_signed_height (gamma t) ha).2.2.mpr hnotseam
  let Q : Set E3 := S.retainedCore i ∪
    ⋃ b : {b : Fin S.capCount // S.owner b = i ∧ b ≠ a.1}, (S.cap b.1).cap
  have hQ : IsCompact Q := hK.union (isCompact_iUnion fun b =>
    (S.cap b.1).cap_isCompact)
  have hsub : uIcc 0 t ⊆ uIcc 0 T := uIcc_subset_uIcc_left ht
  have himage : gamma '' uIcc 0 t ⊆ (S.cap a.1).cap ∪ Q := by
    rintro y ⟨v, hv, rfl⟩
    have hmem := hsphere v (hsub hv)
    rw [hcover] at hmem
    rcases hmem with hcore | hcaps
    · exact Or.inr (Or.inl hcore)
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hcaps
      by_cases hba : b.1 = a.1
      · exact Or.inl (hba ▸ hb)
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨b.1, b.2, hba⟩, hb⟩))
  have hpre : IsPreconnected (gamma '' uIcc 0 t) :=
    isPreconnected_uIcc.image gamma (hcont.mono hsub)
  obtain ⟨y, ⟨w, hw, rfl⟩, hwa, hwQ⟩ := isPreconnected_closed_iff.mp hpre
    (S.cap a.1).cap Q (S.cap a.1).cap_isCompact.isClosed hQ.isClosed himage
    ⟨gamma t, ⟨t, right_mem_uIcc, rfl⟩, ha⟩
    ⟨gamma 0, ⟨0, left_mem_uIcc, rfl⟩, Or.inl hstart⟩
  have hwseam : gamma w ∈ (S.cap a.1).seam := by
    rcases hwQ with hwK | hwcaps
    · exact hinter a.1 a.2 ▸ (show gamma w ∈ S.retainedCore i ∩
        (S.cap a.1).cap from ⟨hwK, hwa⟩)
    · obtain ⟨b, hb⟩ := mem_iUnion.mp hwcaps
      exact (disjoint_left.mp (S.caps_disjoint b.2.2) hb hwa).elim
  have hseam := ((S.cap a.1).cap_seam_signed_height (gamma w) hwa).2.1.mpr hwseam
  have hsign : (S.cap a.1).sign = 1 ∨ (S.cap a.1).sign = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using (S.cap a.1).sign_abs
  have hht := hheight t ht
  have hhw := hheight w (hsub hw)
  have htarget : t ∈ uIcc 0 (z0 - ⟪(u : E3), gamma 0⟫_ℝ) :=
    uIcc_subset_uIcc_left hT ht
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · have htw : t ≤ w := by
      rw [uIcc_of_ge hneg.le] at hw
      exact hw.1
    have hz : z0 ≤ ⟪(u : E3), gamma t⟫_ℝ := by
      rcases mem_uIcc.mp htarget with h | h <;> linarith only [h.1, h.2, hneg, hht]
    rcases hsign with hs | hs
    · have hl := hlower a.1 a.2 hs
      simp only [hs, one_mul] at hstrict hl
      linarith only [hstrict, hl, hz]
    · rw [hs, neg_one_mul] at hstrict hseam
      linarith only [hstrict, hseam, hht, hhw, htw]
  · have hwt : w ≤ t := by
      rw [uIcc_of_le hpos.le] at hw
      exact hw.2
    have hz : ⟪(u : E3), gamma t⟫_ℝ ≤ z0 := by
      rcases mem_uIcc.mp htarget with h | h <;> linarith only [h.1, h.2, hpos, hht]
    rcases hsign with hs | hs
    · rw [hs, one_mul] at hstrict hseam
      linarith only [hstrict, hseam, hht, hhw, hwt]
    · have hu := hupper a.1 a.2 hs
      simp only [hs, neg_one_mul] at hstrict hu
      linarith only [hstrict, hu, hz]



theorem FamilyCutState.regular_core_flow_segment
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (z0 : ℝ)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal < z0)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      z0 < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (F : E3 → E3) (L M : ℝ≥0)
    (hL : LipschitzWith L F) (hM : ∀ y : E3, ‖F y‖ ≤ M)
    (U : Set E3) (hU : IsOpen U) (hcoreU : S.retainedCore i ⊆ U)
    (hunit : ∀ y ∈ U, ⟪(u : E3), F y⟫_ℝ = 1)
    (hsphere : ∀ y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)),
      ∀ t : ℝ, boundedFlow F hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0))) :
    ∀ y ∈ S.retainedCore i,
      ∀ t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ),
        boundedFlow F hL hM y t ∈ S.retainedCore i ∧
        ⟪(u : E3), boundedFlow F hL hM y t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t := by
  intro y hy
  let gamma : ℝ → E3 := boundedFlow F hL hM y
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  have hg0 : gamma 0 = y := boundedFlow_zero F hL hM y
  have hgc : Continuous gamma := continuous_iff_continuousAt.mpr
    (fun t => (boundedFlow_hasDerivAt F hL hM y t).continuousAt)
  have hh : Continuous (fun t => ⟪(u : E3), gamma t⟫_ℝ) :=
    continuous_const.inner hgc
  have hprefix (v : ℝ) (hv : MapsTo gamma (uIcc 0 v) U) :
      ∀ t ∈ uIcc 0 v, ⟪(u : E3), gamma t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t := by
    intro t ht
    have hd (s : ℝ) (hs : s ∈ uIcc 0 t) :
        HasDerivAt (fun w => ⟪(u : E3), gamma w⟫_ℝ) 1 s := by
      have hder := H.hasFDerivAt.comp_hasDerivAt s
        (boundedFlow_hasDerivAt F hL hM y s)
      change HasDerivAt (fun w => ⟪(u : E3), gamma w⟫_ℝ)
        ⟪(u : E3), F (gamma s)⟫_ℝ s at hder
      rw [hunit _ (hv (uIcc_subset_uIcc_left ht hs))] at hder
      exact hder
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · obtain ⟨s, _hs, he⟩ := exists_hasDerivAt_eq_slope
        (fun w => ⟪(u : E3), gamma w⟫_ℝ) (fun _ => (1 : ℝ)) hneg
        hh.continuousOn (fun s hs => hd s (by
          rw [uIcc_of_ge hneg.le]
          exact ⟨hs.1.le, hs.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hneg.ne')).mp he
      rw [hg0] at he'
      linarith only [he']
    · simp only [heq, hg0, add_zero]
    · obtain ⟨s, _hs, he⟩ := exists_hasDerivAt_eq_slope
        (fun w => ⟪(u : E3), gamma w⟫_ℝ) (fun _ => (1 : ℝ)) hpos
        hh.continuousOn (fun s hs => hd s (by
          rw [uIcc_of_le hpos.le]
          exact ⟨hs.1.le, hs.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hpos.ne')).mp he
      rw [hg0] at he'
      linarith only [he']
  have hys : y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)) := by
    obtain ⟨q, _hq, rfl⟩ := hy
    exact ⟨q, rfl⟩
  have hgs (t : ℝ) : gamma t ∈ range (fun q : UnitTwoSphere => psi i (q, 0)) :=
    hsphere y hys t
  have hstart : gamma 0 ∈ S.retainedCore i := hg0.symm ▸ hy
  have hwhole : MapsTo gamma (uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ)) U := by
    apply hgc.continuousOn.mapsTo_uIcc_of_closed_prefix_trap hU
      (S.retainedCore_geometry i).1.isClosed (hcoreU hstart)
      (fun _ h => hcoreU h.1)
    intro v hv hvg
    apply S.retainedCore_of_affine_height_path i z0 hlower hupper gamma v
      (by simpa only [hg0] using hv) hgc.continuousOn (fun t _ => hgs t)
      hstart _ v right_mem_uIcc
    intro t ht
    simpa only [hg0] using hprefix v hvg t ht
  have hheight := hprefix (z0 - ⟪(u : E3), y⟫_ℝ) hwhole
  have hcore := S.retainedCore_of_affine_height_path i z0 hlower hupper gamma
    (z0 - ⟪(u : E3), y⟫_ℝ) (by simpa only [hg0] using
      (right_mem_uIcc : z0 - ⟪(u : E3), y⟫_ℝ ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ)))
    hgc.continuousOn (fun t _ => hgs t) hstart
    (fun t ht => by simpa only [hg0] using hheight t ht)
  exact fun t ht => ⟨hcore t ht, hheight t ht⟩



theorem FamilyCutState.regular_core_middle_retraction
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (z0 : ℝ)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal < z0)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      z0 < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (F : E3 → E3) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (L M : ℝ≥0) (hL : LipschitzWith L F) (hM : ∀ y : E3, ‖F y‖ ≤ M)
    (U : Set E3) (hU : IsOpen U) (hcoreU : S.retainedCore i ⊆ U)
    (hunit : ∀ y ∈ U, ⟪(u : E3), F y⟫_ℝ = 1)
    (hsphere : ∀ y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)),
      ∀ t : ℝ, boundedFlow F hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0))) :
    let R : E3 → E3 := fun y =>
      boundedFlow F hL hM y (z0 - ⟪(u : E3), y⟫_ℝ)
    Continuous R ∧
      R '' S.retainedCore i = collarHeightLevel (psi i) (u : E3) z0 ∧
      (∀ y ∈ collarHeightLevel (psi i) (u : E3) z0, R y = y) ∧
      IsCompact (collarHeightLevel (psi i) (u : E3) z0) ∧
      IsConnected (collarHeightLevel (psi i) (u : E3) z0) := by
  classical
  dsimp only
  let R : E3 → E3 := fun y => boundedFlow F hL hM y (z0 - ⟪(u : E3), y⟫_ℝ)
  have hR : Continuous R := (boundedFlow_contDiff F hL hM hF hFc).continuous.comp
    (continuous_id.prodMk (continuous_const.sub (continuous_const.inner continuous_id)))
  obtain ⟨_hK, hconn, _hdef, hcover, _hinter⟩ := S.retainedCore_geometry i
  have hlevelcore : collarHeightLevel (psi i) (u : E3) z0 ⊆ S.retainedCore i := by
    rintro y ⟨q, hq, rfl⟩
    have hy : psi i (q, 0) ∈ range (fun q : UnitTwoSphere => psi i (q, 0)) := ⟨q, rfl⟩
    rw [hcover] at hy
    rcases hy with hcore | hcaps
    · exact hcore
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hcaps
      have hside := ((S.cap a.1).cap_seam_signed_height _ ha).1
      have hsign : (S.cap a.1).sign = 1 ∨ (S.cap a.1).sign = -1 := by
        apply abs_eq_abs.mp
        simpa only [abs_one] using (S.cap a.1).sign_abs
      change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0 at hq
      rcases hsign with hs | hs
      · have hl := hlower a.1 a.2 hs
        simp only [hs, one_mul] at hside hl
        exfalso
        linarith only [hside, hl, hq]
      · have hu := hupper a.1 a.2 hs
        simp only [hs, neg_one_mul] at hside hu
        exfalso
        linarith only [hside, hu, hq]
  have hfix : ∀ y ∈ collarHeightLevel (psi i) (u : E3) z0, R y = y := by
    rintro y ⟨q, hq, rfl⟩
    change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0 at hq
    dsimp only [R]
    rw [hq, sub_self, boundedFlow_zero]
  have himage : R '' S.retainedCore i = collarHeightLevel (psi i) (u : E3) z0 := by
    apply subset_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hcore, hh⟩ := S.regular_core_flow_segment i z0 hlower hupper
        F L M hL hM U hU hcoreU hunit hsphere y hy
        (z0 - ⟪(u : E3), y⟫_ℝ) right_mem_uIcc
      obtain ⟨q, _hq, heq⟩ := hcore
      dsimp only at heq
      refine ⟨q, ?_, heq⟩
      change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0
      rw [heq]
      linarith only [hh]
    · intro y hy
      exact ⟨y, hlevelcore hy, hfix y hy⟩
  exact ⟨hR, himage, hfix, collarHeightLevel_compact (psi i) (S.embedding i) (u : E3) z0,
    himage ▸ hconn.image R hR.continuousOn⟩

end PoincareConjecture.M25.Topology3D
