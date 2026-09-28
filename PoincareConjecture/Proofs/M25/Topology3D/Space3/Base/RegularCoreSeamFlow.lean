import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreFlowData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarCoordinates
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.regular_core_seam_middle_image
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
        range (fun q : UnitTwoSphere => psi i (q, 0)))
    (a : Fin S.capCount) (ha : S.owner a = i) :
    let Z : Set E3 := collarHeightLevel (psi i) (u : E3) z0
    let A : Set E3 :=
      (fun y : E3 => boundedFlow F hL hM y
        (z0 - ((S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal))) ''
          (S.cap a).seam
    IsCompact A ∧ A.Nonempty ∧ A ⊆ Z ∧
      IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) ∧ A = Z := by
  classical
  let C := S.cap a
  let s := C.cutHeight + C.sign * C.removal
  let T := z0 - s
  let flow : E3 → ℝ → E3 := boundedFlow F hL hM
  let Z : Set E3 := collarHeightLevel (psi i) (u : E3) z0
  let A : Set E3 := (fun y => flow y T) '' C.seam
  change IsCompact A ∧ A.Nonempty ∧ A ⊆ Z ∧
    IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) ∧ A = Z
  have hc : Continuous (fun p : E3 × ℝ => flow p.1 p.2) :=
    (boundedFlow_contDiff F hL hM hF hFc).continuous
  have htime (t : ℝ) : Continuous (fun y : E3 => flow y t) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hsign : C.sign ≠ 0 := by
    intro hz
    have h := C.sign_abs
    rw [hz, abs_zero] at h
    norm_num at h
  obtain ⟨_hK, _hconn, _hdef, _hcover, hinter⟩ := S.retainedCore_geometry i
  have hseam (x : E3) (hx : x ∈ C.seam) :
      x ∈ S.retainedCore i ∧ ⟪(u : E3), x⟫_ℝ = s := by
    have hxc : x ∈ S.retainedCore i ∩ C.cap := by
      rw [hinter a ha]
      exact hx
    have hh := (C.cap_seam_signed_height x hxc.2).2.1.mpr hx
    exact ⟨hxc.1, sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hsign)⟩
  have hAc : IsCompact A := C.seam_isCompact.image (htime T)
  have hAn : A.Nonempty := by
    obtain ⟨q, hq⟩ := C.sourceSeam_isConnected.nonempty
    exact ⟨flow (psi (S.owner a) (q, 0)) T,
      ⟨psi (S.owner a) (q, 0), ⟨q, hq, rfl⟩, rfl⟩⟩
  have hAZ : A ⊆ Z := by
    rintro y ⟨x, hx, rfl⟩
    have hxH := (hseam x hx).2
    have ht : T ∈ uIcc 0 (z0 - ⟪(u : E3), x⟫_ℝ) := by
      rw [hxH]
      exact right_mem_uIcc
    obtain ⟨hy, hh⟩ := S.regular_core_flow_segment i z0 hlower hupper
      F L M hL hM U hU hcoreU hunit hsphere x (hseam x hx).1 T ht
    obtain ⟨q, _hq, heq⟩ := hy
    change psi i (q, 0) = flow x T at heq
    refine ⟨q, ?_, heq⟩
    change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0
    rw [heq]
    change ⟪(u : E3), flow x T⟫_ℝ = ⟪(u : E3), x⟫_ℝ + (z0 - s) at hh
    linarith only [hh, hxH]
  have hlocal (x : E3) (hx : x ∈ C.seam) :
      ∃ O : Set E3, IsOpen O ∧ x ∈ O ∧
        ∀ y ∈ O, y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)) →
          ⟪(u : E3), y⟫_ℝ = s → y ∈ C.seam := by
    obtain ⟨q0, hq0, hq0x⟩ := hx
    have hq0x' : psi i (q0, 0) = x := by simpa only [ha] using hq0x
    obtain ⟨W, hW, hqW, _hWt, _hWi, hWform⟩ :=
      S.exists_seam_source_half_neighborhood a q0 hq0
    obtain ⟨E, hEf, hEs, _hEt, _hEi⟩ := exists_collar_chart (psi i) (S.embedding i)
    have hsource (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ E.source := by
      rw [hEs]
      exact ⟨mem_univ _, by norm_num⟩
    have hval (q : UnitTwoSphere) : E (q, 0) = psi i (q, 0) := congrFun hEf (q, 0)
    have htarget (q : UnitTwoSphere) : psi i (q, 0) ∈ E.target := by
      rw [← hval]
      exact E.map_source (hsource q)
    have hinverse (q : UnitTwoSphere) : E.symm (psi i (q, 0)) = (q, 0) := by
      rw [← hval]
      exact E.left_inv (hsource q)
    let O : Set E3 := E.target ∩ E.symm ⁻¹' (W ×ˢ (univ : Set ℝ))
    have hO : IsOpen O := E.symm.continuousOn.isOpen_inter_preimage E.open_target
      (hW.prod isOpen_univ)
    refine ⟨O, hO, ?_, ?_⟩
    · rw [← hq0x']
      refine ⟨htarget q0, ?_⟩
      change E.symm (psi i (q0, 0)) ∈ W ×ˢ (univ : Set ℝ)
      rw [hinverse]
      exact ⟨hqW, mem_univ _⟩
    · rintro y hy ⟨q, rfl⟩ hh
      have hqW' : q ∈ W := by
        have h := hy.2
        change E.symm (psi i (q, 0)) ∈ W ×ˢ (univ : Set ℝ) at h
        rw [hinverse] at h
        exact h.1
      obtain ⟨_hp, _hz1, _hz2, _hinv, _hxi, _heq, hheight, _hcore, hqs, _hother⟩ :=
        hWform q hqW'
      let z := (heightCoordinates ((C.sourceChart.symm q : UnitTwoSphere) : E3)).2
      have hheight' : ⟪(u : E3), psi i (q, 0)⟫_ℝ =
          s + C.sign * (C.scale * z) := by
        calc
          _ = C.cutHeight + C.sign * (C.removal + C.scale * z) := by
            simpa only [ha] using hheight
          _ = _ := by dsimp only [s]; ring
      have hprod : C.sign * (C.scale * z) = 0 := by linarith only [hh, hheight']
      have hz : z = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hsign)).resolve_left
          C.scale_pos.ne'
      have hqs' : q ∈ C.sourceSeam := hqs.mpr hz
      have hmem : psi (S.owner a) (q, 0) ∈ C.seam := ⟨q, hqs', rfl⟩
      simpa only [ha] using hmem
  have haffine (v : E3) (b : ℝ)
      (hv : ∀ t ∈ uIcc 0 b, flow v t ∈ U) :
      ∀ t ∈ uIcc 0 b, ⟪(u : E3), flow v t⟫_ℝ = ⟪(u : E3), v⟫_ℝ + t := by
    intro t ht
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    have hcont : Continuous (fun t : ℝ => ⟪(u : E3), flow v t⟫_ℝ) :=
      continuous_const.inner (hc.comp (continuous_const.prodMk continuous_id))
    have hd (w : ℝ) (hw : w ∈ uIcc 0 t) :
        HasDerivAt (fun z => ⟪(u : E3), flow v z⟫_ℝ) 1 w := by
      have h := H.hasFDerivAt.comp_hasDerivAt w (boundedFlow_hasDerivAt F hL hM v w)
      change HasDerivAt (fun z => ⟪(u : E3), flow v z⟫_ℝ)
        ⟪(u : E3), F (flow v w)⟫_ℝ w at h
      rw [hunit _ (hv w (uIcc_subset_uIcc_left ht hw))] at h
      exact h
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · obtain ⟨w, _hw, he⟩ := exists_hasDerivAt_eq_slope
        (fun z => ⟪(u : E3), flow v z⟫_ℝ) (fun _ => (1 : ℝ)) hneg
        hcont.continuousOn (fun w hw => hd w (by
          rw [uIcc_of_ge hneg.le]
          exact ⟨hw.1.le, hw.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hneg.ne')).mp he
      change 1 * (0 - t) = ⟪(u : E3), flow v 0⟫_ℝ - ⟪(u : E3), flow v t⟫_ℝ at he'
      simp only [flow, boundedFlow_zero] at he'
      linarith only [he']
    · simp only [heq, flow, boundedFlow_zero, add_zero]
    · obtain ⟨w, _hw, he⟩ := exists_hasDerivAt_eq_slope
        (fun z => ⟪(u : E3), flow v z⟫_ℝ) (fun _ => (1 : ℝ)) hpos
        hcont.continuousOn (fun w hw => hd w (by
          rw [uIcc_of_le hpos.le]
          exact ⟨hw.1.le, hw.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hpos.ne')).mp he
      change 1 * (t - 0) = ⟪(u : E3), flow v t⟫_ℝ - ⟪(u : E3), flow v 0⟫_ℝ at he'
      simp only [flow, boundedFlow_zero] at he'
      linarith only [he']
  have hnear (x : E3) (hx : x ∈ C.seam) :
      ∃ V : Set E3, IsOpen V ∧ flow x T ∈ V ∧ ∀ y ∈ V, y ∈ Z → y ∈ A := by
    let Q : Set (E3 × ℝ) := (fun p => flow p.1 p.2) ⁻¹' U
    have hQ : IsOpen Q := hU.preimage hc
    have htrack : {flow x T} ×ˢ uIcc 0 (-T) ⊆ Q := by
      rintro ⟨v, t⟩ ⟨hv, ht⟩
      have hv' : v = flow x T := hv
      subst v
      have htt : T + t ∈ uIcc 0 T := by
        rcases le_total 0 T with hpos | hneg
        · rw [uIcc_of_ge (neg_nonpos.mpr hpos)] at ht
          rw [uIcc_of_le hpos]
          constructor <;> linarith only [ht.1, ht.2]
        · rw [uIcc_of_le (neg_nonneg.mpr hneg)] at ht
          rw [uIcc_of_ge hneg]
          constructor <;> linarith only [ht.1, ht.2]
      have htt' : T + t ∈ uIcc 0 (z0 - ⟪(u : E3), x⟫_ℝ) := by
        rw [(hseam x hx).2]
        exact htt
      have hmem := (S.regular_core_flow_segment i z0 hlower hupper
        F L M hL hM U hU hcoreU hunit hsphere x (hseam x hx).1 (T + t) htt').1
      change boundedFlow F hL hM (boundedFlow F hL hM x T) t ∈ U
      rw [← boundedFlow_add]
      exact hcoreU hmem
    obtain ⟨V1, J, hV1, _hJ, hyV1, hIJ, hVJ⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_uIcc hQ htrack
    obtain ⟨O, hO, hxO, hOseam⟩ := hlocal x hx
    let V : Set E3 := V1 ∩ (fun y => flow y (-T)) ⁻¹' O
    have hV : IsOpen V := hV1.inter (hO.preimage (htime (-T)))
    have hback : flow (flow x T) (-T) = x := boundedFlow_neg F hL hM x T
    refine ⟨V, hV, ⟨hyV1 (mem_singleton _), ?_⟩, ?_⟩
    · change flow (flow x T) (-T) ∈ O
      rw [hback]
      exact hxO
    · intro y hy hyZ
      have hytrack (t : ℝ) (ht : t ∈ uIcc 0 (-T)) : flow y t ∈ U := by
        change (y, t) ∈ Q
        exact hVJ ⟨hy.1, hIJ ht⟩
      have hh := haffine y (-T) hytrack (-T) right_mem_uIcc
      obtain ⟨q, hq, hqy⟩ := hyZ
      have hySphere : y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)) := ⟨q, hqy⟩
      have hyHeight : ⟪(u : E3), y⟫_ℝ = z0 := by
        rw [← hqy]
        exact hq
      have hheight : ⟪(u : E3), flow y (-T)⟫_ℝ = s := by
        dsimp only [T] at hh
        linarith only [hh, hyHeight]
      have hseamBack := hOseam (flow y (-T)) hy.2
        (hsphere y hySphere (-T)) hheight
      refine ⟨flow y (-T), hseamBack, ?_⟩
      simpa only [neg_neg] using boundedFlow_neg F hL hM y (-T)
  have hAo : IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨V, hV, hyV, hVsub⟩ := hnear x hx
    change flow x T = (y : E3) at hxy
    have hyV' : (y : E3) ∈ V := hxy ▸ hyV
    have hn : (fun y : Z => (y : E3)) ⁻¹' V ∈ 𝓝 y :=
      (hV.preimage continuous_subtype_val).mem_nhds hyV'
    exact mem_of_superset hn (fun v hv => hVsub v hv v.property)
  obtain ⟨_hR, _himage, _hfix, _hcompact, hZ⟩ :=
    S.regular_core_middle_retraction i z0 hlower hupper F hF hFc L M hL hM
      U hU hcoreU hunit hsphere
  let : ConnectedSpace Z := isConnected_iff_connectedSpace.mp hZ
  have hAcl : IsClosed ((fun y : Z => (y : E3)) ⁻¹' A) :=
    hAc.isClosed.preimage continuous_subtype_val
  have hAnonempty : ((fun y : Z => (y : E3)) ⁻¹' A).Nonempty := by
    obtain ⟨y, hy⟩ := hAn
    exact ⟨⟨y, hAZ hy⟩, hy⟩
  have hwhole := (show IsClopen ((fun y : Z => (y : E3)) ⁻¹' A) from
    ⟨hAcl, hAo⟩).eq_univ hAnonempty
  refine ⟨hAc, hAn, hAZ, hAo, subset_antisymm hAZ ?_⟩
  intro y hy
  have hm : (⟨y, hy⟩ : Z) ∈ (fun y : Z => (y : E3)) ⁻¹' A := by
    rw [hwhole]
    exact mem_univ _
  exact hm

end PoincareConjecture.M25.Topology3D
