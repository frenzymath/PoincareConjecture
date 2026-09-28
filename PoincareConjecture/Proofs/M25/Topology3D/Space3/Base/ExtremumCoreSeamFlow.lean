import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreSeamNeighborhoods
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreTransport
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.morse_rest_seam_middle_images
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : 2 * rho ^ 2 < D)
    (hsource : closedBall (0 : E2) (2 * rho) ⊆ F.source)
    (hbufferCore : F '' closedBall (0 : E2) (2 * rho) ⊆ S.sourceCore i)
    (havoid : ∀ a : Fin S.capCount,
      Disjoint ((fun q : UnitTwoSphere => psi i (q, 0)) ''
        (F '' closedBall (0 : E2) rho)) (S.cap a).cap)
    (c kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ x ∈ closedBall (0 : E2) (2 * rho),
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2)
    (hlower : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal + 3 * D < c)
    (hupper : ∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal)
    (V : E3 → E3) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (L M : ℝ≥0) (hL : LipschitzWith L V) (hM : ∀ y : E3, ‖V y‖ ≤ M)
    (U : Set E3) (hU : IsOpen U)
    (hrestU : S.retainedCore i \
      ((fun q : UnitTwoSphere => psi i (q, 0)) '' (F '' ball (0 : E2) rho)) ⊆ U)
    (hunit : ∀ y ∈ U, ⟪(u : E3), V y⟫_ℝ = 1)
    (hsphere : ∀ y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)),
      ∀ t : ℝ, boundedFlow V hL hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0))) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let newSeam : Set E3 := j '' (F '' sphere (0 : E2) rho)
    let z0 : ℝ := c + 2 * kappa * rho ^ 2
    let Z : Set E3 := collarHeightLevel (psi i) (u : E3) z0
    (∀ a : Fin S.capCount, S.owner a = i →
      let A : Set E3 :=
        (fun y : E3 => boundedFlow V hL hM y
          (z0 - ((S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal))) ''
            (S.cap a).seam
      IsCompact A ∧ A.Nonempty ∧ A ⊆ Z ∧
        IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) ∧ A = Z) ∧
    let A : Set E3 :=
      (fun y : E3 => boundedFlow V hL hM y (z0 - (c + kappa * rho ^ 2))) ''
        newSeam
    IsCompact A ∧ A.Nonempty ∧ A ⊆ Z ∧
      IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) ∧ A = Z := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let disc := j '' (F '' closedBall (0 : E2) rho)
  let discOpen := j '' (F '' ball (0 : E2) rho)
  let rest := S.retainedCore i \ discOpen
  let newSeam := j '' (F '' sphere (0 : E2) rho)
  let z0 := c + 2 * kappa * rho ^ 2
  let Z := collarHeightLevel (psi i) (u : E3) z0
  let flow : E3 → ℝ → E3 := boundedFlow V hL hM
  have hradii : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  have hs : closedBall (0 : E2) rho ⊆ F.source := hradii.trans hsource
  have hd : F '' closedBall (0 : E2) rho ⊆ S.sourceCore i :=
    (image_mono hradii).trans hbufferCore
  have hf (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2 := hform x (hradii hx)
  have hsegment := S.morse_rest_flow_segment i F rho hrho hsmall hs c kappa hkappa
    hf hlower hupper V L M hL hM U hU hrestU hunit hsphere
  change ∀ y ∈ rest, ∀ t ∈ uIcc 0 (z0 - ⟪(u : E3), y⟫_ℝ),
    flow y t ∈ rest ∧ ⟪(u : E3), flow y t⟫_ℝ = ⟪(u : E3), y⟫_ℝ + t at hsegment
  obtain ⟨_hR, _himage, _hfix, _hcompact, hZ⟩ :=
    S.morse_rest_middle_retraction i F rho hrho hsmall hs hd c kappa hkappa hf
      hlower hupper V hV hVc L M hL hM U hU hrestU hunit hsphere
  change IsConnected Z at hZ
  have hc : Continuous (fun p : E3 × ℝ => flow p.1 p.2) :=
    (boundedFlow_contDiff V hL hM hV hVc).continuous
  have htime (t : ℝ) : Continuous (fun y : E3 => flow y t) :=
    hc.comp (continuous_id.prodMk continuous_const)
  have haffine (v : E3) (b : ℝ)
      (hv : ∀ t ∈ uIcc 0 b, flow v t ∈ U) :
      ∀ t ∈ uIcc 0 b, ⟪(u : E3), flow v t⟫_ℝ = ⟪(u : E3), v⟫_ℝ + t := by
    intro t ht
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    have hcont : Continuous (fun t : ℝ => ⟪(u : E3), flow v t⟫_ℝ) :=
      continuous_const.inner (hc.comp (continuous_const.prodMk continuous_id))
    have hder (w : ℝ) (hw : w ∈ uIcc 0 t) :
        HasDerivAt (fun z => ⟪(u : E3), flow v z⟫_ℝ) 1 w := by
      have h := H.hasFDerivAt.comp_hasDerivAt w (boundedFlow_hasDerivAt V hL hM v w)
      change HasDerivAt (fun z => ⟪(u : E3), flow v z⟫_ℝ)
        ⟪(u : E3), V (flow v w)⟫_ℝ w at h
      rw [hunit _ (hv w (uIcc_subset_uIcc_left ht hw))] at h
      exact h
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · obtain ⟨w, _hw, he⟩ := exists_hasDerivAt_eq_slope
        (fun z => ⟪(u : E3), flow v z⟫_ℝ) (fun _ => (1 : ℝ)) hneg
        hcont.continuousOn (fun w hw => hder w (by
          rw [uIcc_of_ge hneg.le]
          exact ⟨hw.1.le, hw.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hneg.ne')).mp he
      change 1 * (0 - t) = ⟪(u : E3), flow v 0⟫_ℝ - ⟪(u : E3), flow v t⟫_ℝ at he'
      simp only [flow, boundedFlow_zero] at he'
      linarith only [he']
    · simp only [heq, flow, boundedFlow_zero, add_zero]
    · obtain ⟨w, _hw, he⟩ := exists_hasDerivAt_eq_slope
        (fun z => ⟪(u : E3), flow v z⟫_ℝ) (fun _ => (1 : ℝ)) hpos
        hcont.continuousOn (fun w hw => hder w (by
          rw [uIcc_of_le hpos.le]
          exact ⟨hw.1.le, hw.2.le⟩))
      have he' := (eq_div_iff (sub_ne_zero.mpr hpos.ne')).mp he
      change 1 * (t - 0) = ⟪(u : E3), flow v t⟫_ℝ - ⟪(u : E3), flow v 0⟫_ℝ at he'
      simp only [flow, boundedFlow_zero] at he'
      linarith only [he']
  have himage (Sigma : Set E3) (s : ℝ) (hSc : IsCompact Sigma) (hSn : Sigma.Nonempty)
      (hSR : Sigma ⊆ rest) (hSH : ∀ x ∈ Sigma, ⟪(u : E3), x⟫_ℝ = s)
      (hlocal : ∀ x ∈ Sigma, ∃ O : Set E3, IsOpen O ∧ x ∈ O ∧
        ∀ y ∈ O, y ∈ range j → ⟪(u : E3), y⟫_ℝ = s → y ∈ Sigma) :
      let A := (fun y : E3 => flow y (z0 - s)) '' Sigma
      IsCompact A ∧ A.Nonempty ∧ A ⊆ Z ∧
        IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) ∧ A = Z := by
    let T := z0 - s
    let A := (fun y : E3 => flow y T) '' Sigma
    change IsCompact A ∧ A.Nonempty ∧ A ⊆ Z ∧
      IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) ∧ A = Z
    have hAc : IsCompact A := hSc.image (htime T)
    have hAn : A.Nonempty := hSn.image (fun y => flow y T)
    have hAZ : A ⊆ Z := by
      rintro y ⟨x, hx, rfl⟩
      have ht : T ∈ uIcc 0 (z0 - ⟪(u : E3), x⟫_ℝ) := by
        rw [hSH x hx]
        exact right_mem_uIcc
      obtain ⟨hy, hh⟩ := hsegment x (hSR hx) T ht
      obtain ⟨q, _hq, heq⟩ := hy.1
      change psi i (q, 0) = flow x T at heq
      refine ⟨q, ?_, heq⟩
      change ⟪(u : E3), psi i (q, 0)⟫_ℝ = z0
      rw [heq]
      change ⟪(u : E3), flow x T⟫_ℝ = ⟪(u : E3), x⟫_ℝ + (z0 - s) at hh
      linarith only [hh, hSH x hx]
    have hnear (x : E3) (hx : x ∈ Sigma) :
        ∃ W : Set E3, IsOpen W ∧ flow x T ∈ W ∧ ∀ y ∈ W, y ∈ Z → y ∈ A := by
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
          rw [hSH x hx]
          exact htt
        have hmem := (hsegment x (hSR hx) (T + t) htt').1
        change boundedFlow V hL hM (boundedFlow V hL hM x T) t ∈ U
        rw [← boundedFlow_add]
        exact hrestU hmem
      obtain ⟨W1, J, hW1, _hJ, hbW1, hIJ, hWJ⟩ :=
        generalized_tube_lemma isCompact_singleton isCompact_uIcc hQ htrack
      obtain ⟨O, hO, hxO, hOseam⟩ := hlocal x hx
      let W := W1 ∩ (fun y => flow y (-T)) ⁻¹' O
      have hW : IsOpen W := hW1.inter (hO.preimage (htime (-T)))
      have hback : flow (flow x T) (-T) = x := boundedFlow_neg V hL hM x T
      refine ⟨W, hW, ⟨hbW1 (mem_singleton _), ?_⟩, ?_⟩
      · change flow (flow x T) (-T) ∈ O
        rw [hback]
        exact hxO
      · intro y hy hyZ
        have hytrack (t : ℝ) (ht : t ∈ uIcc 0 (-T)) : flow y t ∈ U := by
          change (y, t) ∈ Q
          exact hWJ ⟨hy.1, hIJ ht⟩
        have hh := haffine y (-T) hytrack (-T) right_mem_uIcc
        obtain ⟨q, hq, hqy⟩ := hyZ
        have hySphere : y ∈ range j := ⟨q, hqy⟩
        have hyHeight : ⟪(u : E3), y⟫_ℝ = z0 := by
          rw [← hqy]
          exact hq
        have hheight : ⟪(u : E3), flow y (-T)⟫_ℝ = s := by
          dsimp only [T] at hh
          linarith only [hh, hyHeight]
        have hseamBack := hOseam (flow y (-T)) hy.2
          (hsphere y hySphere (-T)) hheight
        refine ⟨flow y (-T), hseamBack, ?_⟩
        simpa only [neg_neg] using boundedFlow_neg V hL hM y (-T)
    have hAo : IsOpen ((fun y : Z => (y : E3)) ⁻¹' A) := by
      apply isOpen_iff_mem_nhds.mpr
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hy
      obtain ⟨W, hW, hyW, hWsub⟩ := hnear x hx
      change flow x T = (y : E3) at hxy
      have hyW' : (y : E3) ∈ W := hxy ▸ hyW
      have hn : (fun y : Z => (y : E3)) ⁻¹' W ∈ 𝓝 y :=
        (hW.preimage continuous_subtype_val).mem_nhds hyW'
      exact mem_of_superset hn (fun v hv => hWsub v hv v.property)
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
  constructor
  · intro a ha
    let C := S.cap a
    let s := C.cutHeight + C.sign * C.removal
    have hsign : C.sign ≠ 0 := by
      intro hz
      have hh := C.sign_abs
      rw [hz, abs_zero] at hh
      norm_num at hh
    obtain ⟨_hK, _hconn, _hdef, _hcover, hinter⟩ := S.retainedCore_geometry i
    have hseam (x : E3) (hx : x ∈ C.seam) :
        x ∈ rest ∧ ⟪(u : E3), x⟫_ℝ = s := by
      have hxc : x ∈ S.retainedCore i ∩ C.cap := by
        rw [hinter a ha]
        exact hx
      have hh := (C.cap_seam_signed_height x hxc.2).2.1.mpr hx
      refine ⟨⟨hxc.1, ?_⟩, sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hsign)⟩
      intro hxO
      have hxD : x ∈ disc := image_mono (image_mono ball_subset_closedBall) hxO
      exact disjoint_left.mp (havoid a) hxD hxc.2
    have hSn : C.seam.Nonempty := by
      obtain ⟨q, hq⟩ := C.sourceSeam_isConnected.nonempty
      exact ⟨psi (S.owner a) (q, 0), ⟨q, hq, rfl⟩⟩
    apply himage C.seam s C.seam_isCompact hSn (fun x hx => (hseam x hx).1)
      (fun x hx => (hseam x hx).2)
    intro x hx
    obtain ⟨q0, hq0, hq0x⟩ := hx
    have heq : j q0 = x := by simpa only [ha] using hq0x
    obtain ⟨W, _hW, _hqW, _hWt, _hWi, _hWform,
      O, hO, hqO, _hcollar, _hout, _hOq, hOform⟩ :=
      S.exists_morse_rest_old_seam_neighborhood i F rho hrho hs a ha (havoid a) q0 hq0
    refine ⟨O, hO, heq ▸ hqO, ?_⟩
    intro y hy hys hh
    exact (hOform y hy hys).2.mpr hh
  · obtain ⟨_hdisc, hnewC, hnewConn, hdiff, _hzsmall, _hzside,
      _hl, _hu, hfull, _hmiss⟩ := S.morse_disc_middle_geometry i F rho hrho hsmall hs
        c kappa hkappa hf hlower hupper
    change disc \ discOpen = newSeam at hdiff
    have hseam (x : E3) (hx : x ∈ newSeam) :
        x ∈ rest ∧ ⟪(u : E3), x⟫_ℝ = c + kappa * rho ^ 2 := by
      have hxD : x ∈ disc \ discOpen := by rw [hdiff]; exact hx
      have hxcore : x ∈ S.retainedCore i := by
        obtain ⟨q, hq, heq⟩ := hxD.1
        exact ⟨q, hd hq, heq⟩
      exact ⟨⟨hxcore, hxD.2⟩, (hfull x hxD.1).2.2.2.1.mpr hx⟩
    apply himage newSeam (c + kappa * rho ^ 2) hnewC hnewConn.nonempty
      (fun x hx => (hseam x hx).1) (fun x hx => (hseam x hx).2)
    intro x hx
    obtain ⟨q0, hq0, hq0x⟩ := hx
    obtain ⟨_hW, _hqW, _hWt, _hWform, O, hO, hqO, _hcollar, _hOq, hOform⟩ :=
      S.exists_morse_rest_new_seam_neighborhood i F rho hrho hsource hbufferCore
        c kappa hkappa hform q0 hq0
    refine ⟨O, hO, hq0x ▸ hqO, ?_⟩
    intro y hy hys hh
    exact (hOform y hy hys).2.mpr hh

end PoincareConjecture.M25.Topology3D
