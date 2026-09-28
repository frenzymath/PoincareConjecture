import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.RegularCoreFlowData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarCoordinates

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.exists_morse_rest_old_seam_neighborhood
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho)
    (hsource : closedBall (0 : E2) rho ⊆ F.source)
    (a : Fin S.capCount) (ha : S.owner a = i)
    (havoid : Disjoint
      ((fun q : UnitTwoSphere => psi i (q, 0)) ''
        (F '' closedBall (0 : E2) rho)) (S.cap a).cap)
    (q0 : UnitTwoSphere) (hq0 : q0 ∈ (S.cap a).sourceSeam) :
    let C := S.cap a
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let disc : Set E3 := j '' (F '' closedBall (0 : E2) rho)
    let nativeRest : Set UnitTwoSphere :=
      S.sourceCore i \ (F '' ball (0 : E2) rho)
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let s : ℝ := C.cutHeight + C.sign * C.removal
    ∃ W : Set UnitTwoSphere,
      IsOpen W ∧ q0 ∈ W ∧ W ⊆ C.sourceChart.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.sourceChart.symm W ∧
      (∀ q ∈ W,
        let p : UnitTwoSphere := C.sourceChart.symm q
        let z : ℝ := (heightCoordinates (p : E3)).2
        p ∈ C.sourceChart.source ∧
          |z| < C.overlapWidth / 2 ∧ |z| < 1 / 4 ∧
          C.sourceChart p = q ∧ j q ∉ disc ∧
          C.sign * (⟪(u : E3), j q⟫_ℝ - s) = C.scale * z ∧
          (q ∈ nativeRest ↔ 0 ≤ z) ∧
          (q ∈ C.sourceSeam ↔ z = 0)) ∧
      ∃ O : Set E3,
        IsOpen O ∧ j q0 ∈ O ∧
        O ⊆ psi i '' (univ ×ˢ Ioo (-1) 1) ∧ O ⊆ discᶜ ∧
        (∀ q : UnitTwoSphere, j q ∈ O → q ∈ W) ∧
        ∀ y ∈ O, y ∈ range j →
          (y ∈ rest ↔ 0 ≤ C.sign * (⟪(u : E3), y⟫_ℝ - s)) ∧
          (y ∈ C.seam ↔ ⟪(u : E3), y⟫_ℝ = s) := by
  let C := S.cap a
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let disc : Set E3 := j '' (F '' closedBall (0 : E2) rho)
  let nativeRest := S.sourceCore i \ (F '' ball (0 : E2) rho)
  let rest := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let s := C.cutHeight + C.sign * C.removal
  have hj : Continuous j := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hjinj : Function.Injective j := by
    intro q q' hqq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hqq)
  have hdisc : IsCompact disc :=
    (nativeDiscChart_geometry F rho hrho hsource).2.2.2.2.1.image hj
  have hq0cap : j q0 ∈ C.cap := by
    obtain ⟨p, hp, hpq⟩ := hq0
    have h : psi (S.owner a) (q0, 0) ∈ C.cap := ⟨q0, ⟨p, hp.le, hpq⟩, rfl⟩
    simpa only [ha] using h
  have hq0out : j q0 ∉ disc := fun h => disjoint_left.mp havoid h hq0cap
  obtain ⟨W0, hW0, hqW0, hW0t, hW0i, hW0form⟩ :=
    S.exists_seam_source_half_neighborhood a q0 hq0
  let W := W0 ∩ j ⁻¹' discᶜ
  have hW : IsOpen W := hW0.inter (hdisc.isClosed.isOpen_compl.preimage hj)
  have hqW : q0 ∈ W := ⟨hqW0, hq0out⟩
  have hWt : W ⊆ C.sourceChart.target := fun _ hq => hW0t hq.1
  have hsign2 : C.sign ^ 2 = 1 := by nlinarith only [sq_abs C.sign, C.sign_abs]
  have hsign : C.sign ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : 2 ≠ 0)] at hsign2
    norm_num at hsign2
  have hWform (q : UnitTwoSphere) (hq : q ∈ W) :
      let p : UnitTwoSphere := C.sourceChart.symm q
      let z : ℝ := (heightCoordinates (p : E3)).2
      p ∈ C.sourceChart.source ∧
        |z| < C.overlapWidth / 2 ∧ |z| < 1 / 4 ∧
        C.sourceChart p = q ∧ j q ∉ disc ∧
        C.sign * (⟪(u : E3), j q⟫_ℝ - s) = C.scale * z ∧
        (q ∈ nativeRest ↔ 0 ≤ z) ∧
        (q ∈ C.sourceSeam ↔ z = 0) := by
    obtain ⟨hp, hz1, hz2, hinv, _hxi, _heq, hheight, hcore, hseam, _hother⟩ :=
      hW0form q hq.1
    let z := (heightCoordinates ((C.sourceChart.symm q : UnitTwoSphere) : E3)).2
    have hh : ⟪(u : E3), j q⟫_ℝ =
        C.cutHeight + C.sign * (C.removal + C.scale * z) := by
      simpa only [ha] using hheight
    have hsigned : C.sign * (⟪(u : E3), j q⟫_ℝ - s) = C.scale * z := by
      rw [hh]
      calc
        _ = C.sign ^ 2 * (C.scale * z) := by dsimp only [s]; ring
        _ = _ := by rw [hsign2, one_mul]
    have hcore' : q ∈ S.sourceCore i ↔ 0 ≤ z := by simpa only [ha] using hcore
    have hnot : q ∉ F '' ball (0 : E2) rho := by
      intro h
      exact hq.2 ⟨q, image_mono ball_subset_closedBall h, rfl⟩
    refine ⟨hp, hz1, hz2, hinv, hq.2, hsigned, ?_, hseam⟩
    exact ⟨fun h => hcore'.mp h.1, fun h => ⟨hcore'.mpr h, hnot⟩⟩
  have hrestq (q : UnitTwoSphere) : j q ∈ rest ↔ q ∈ nativeRest := by
    change j q ∈ j '' S.sourceCore i \ j '' (F '' ball (0 : E2) rho) ↔ _
    rw [← image_sdiff hjinj, hjinj.mem_set_image]
  have hseamq (q : UnitTwoSphere) : j q ∈ C.seam ↔ q ∈ C.sourceSeam := by
    constructor
    · rintro ⟨q', hq', heq⟩
      have heq' : j q' = j q := by simpa only [ha] using heq
      exact hjinj heq' ▸ hq'
    · intro hq
      have h : psi (S.owner a) (q, 0) ∈ C.seam := ⟨q, hq, rfl⟩
      simpa only [ha] using h
  obtain ⟨E, hEf, hEs, hEt, _hEi⟩ := exists_collar_chart (psi i) (S.embedding i)
  have hEs0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ E.source := by
    rw [hEs]
    exact ⟨mem_univ _, by norm_num⟩
  have hEval (q : UnitTwoSphere) : E (q, 0) = j q := congrFun hEf (q, 0)
  have hEt0 (q : UnitTwoSphere) : j q ∈ E.target := by
    rw [← hEval]
    exact E.map_source (hEs0 q)
  have hEinv (q : UnitTwoSphere) : E.symm (j q) = (q, 0) := by
    rw [← hEval]
    exact E.left_inv (hEs0 q)
  let O := (E.target ∩ E.symm ⁻¹' (W ×ˢ (univ : Set ℝ))) ∩ discᶜ
  have hO : IsOpen O := (E.symm.continuousOn.isOpen_inter_preimage E.open_target
    (hW.prod isOpen_univ)).inter hdisc.isClosed.isOpen_compl
  have hOq (q : UnitTwoSphere) (hq : j q ∈ O) : q ∈ W := by
    have hh : E.symm (j q) ∈ W ×ˢ (univ : Set ℝ) := hq.1.2
    rw [hEinv] at hh
    exact hh.1
  refine ⟨W, hW, hqW, hWt, hW0i.mono inter_subset_left, hWform,
    O, hO, ?_, fun _ hy => hEt ▸ hy.1.1, fun _ hy => hy.2, hOq, ?_⟩
  · refine ⟨⟨hEt0 q0, ?_⟩, hq0out⟩
    change E.symm (j q0) ∈ W ×ˢ (univ : Set ℝ)
    rw [hEinv]
    exact ⟨hqW, mem_univ _⟩
  · rintro y hy ⟨q, rfl⟩
    obtain ⟨_hp, _hz1, _hz2, _hinv, _hout, hsigned, hcore, hseam⟩ :=
      hWform q (hOq q hy)
    let z := (heightCoordinates ((C.sourceChart.symm q : UnitTwoSphere) : E3)).2
    constructor
    · rw [hrestq, hcore, hsigned]
      exact ⟨fun hz => mul_nonneg C.scale_pos.le hz,
        fun hh => nonneg_of_mul_nonneg_right hh C.scale_pos⟩
    · rw [hseamq, hseam]
      constructor
      · intro hz
        have hh : C.sign * (⟪(u : E3), j q⟫_ℝ - s) = 0 := by
          rw [hsigned, hz, mul_zero]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hsign)
      · intro hh
        have hz : C.scale * z = 0 := by rw [← hsigned, hh, sub_self, mul_zero]
        exact (mul_eq_zero.mp hz).resolve_left C.scale_pos.ne'

theorem FamilyCutState.exists_morse_rest_new_seam_neighborhood
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho)
    (hsource : closedBall (0 : E2) (2 * rho) ⊆ F.source)
    (hbufferCore : F '' closedBall (0 : E2) (2 * rho) ⊆ S.sourceCore i)
    (c kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ x ∈ closedBall (0 : E2) (2 * rho),
      ⟪(u : E3), psi i (F x, 0)⟫_ℝ = c + kappa * ‖x‖ ^ 2)
    (q0 : UnitTwoSphere) (hq0 : q0 ∈ F '' sphere (0 : E2) rho) :
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let W : Set UnitTwoSphere := F '' ball (0 : E2) (2 * rho)
    let nativeRest : Set UnitTwoSphere :=
      S.sourceCore i \ (F '' ball (0 : E2) rho)
    let nativeSeam : Set UnitTwoSphere := F '' sphere (0 : E2) rho
    let rest : Set E3 := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
    let seam : Set E3 := j '' nativeSeam
    let s : ℝ := c + kappa * rho ^ 2
    IsOpen W ∧ q0 ∈ W ∧ W ⊆ F.target ∧
      (∀ q ∈ W,
        let x : E2 := F.symm q
        x ∈ F.source ∧ ‖x‖ < 2 * rho ∧ F x = q ∧
          kappa * (⟪(u : E3), j q⟫_ℝ - s) = ‖x‖ ^ 2 - rho ^ 2 ∧
          (q ∈ nativeRest ↔ rho ≤ ‖x‖) ∧
          (q ∈ nativeSeam ↔ ‖x‖ = rho)) ∧
      ∃ O : Set E3,
        IsOpen O ∧ j q0 ∈ O ∧
        O ⊆ psi i '' (univ ×ˢ Ioo (-1) 1) ∧
        (∀ q : UnitTwoSphere, j q ∈ O → q ∈ W) ∧
        ∀ y ∈ O, y ∈ range j →
          (y ∈ rest ↔ 0 ≤ kappa * (⟪(u : E3), y⟫_ℝ - s)) ∧
          (y ∈ seam ↔ ⟪(u : E3), y⟫_ℝ = s) := by
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let W := F '' ball (0 : E2) (2 * rho)
  let nativeRest := S.sourceCore i \ (F '' ball (0 : E2) rho)
  let nativeSeam := F '' sphere (0 : E2) rho
  let rest := S.retainedCore i \ j '' (F '' ball (0 : E2) rho)
  let seam := j '' nativeSeam
  let s := c + kappa * rho ^ 2
  have hsmall : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  have hbs : ball (0 : E2) (2 * rho) ⊆ F.source :=
    fun _ hx => hsource (ball_subset_closedBall hx)
  have hW : IsOpen W := F.isOpen_image_of_subset_source isOpen_ball hbs
  have hqW : q0 ∈ W := by
    obtain ⟨x, hx, rfl⟩ := hq0
    refine ⟨x, mem_ball_zero_iff.mpr ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm.mp hx]
    linarith only [hrho]
  have hWt : W ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source (hbs hx)
  have hkap2 : kappa ^ 2 = 1 := by nlinarith only [sq_abs kappa, hkappa]
  have hkap : kappa ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hkappa
    norm_num at hkappa
  have hWform (q : UnitTwoSphere) (hq : q ∈ W) :
      let x : E2 := F.symm q
      x ∈ F.source ∧ ‖x‖ < 2 * rho ∧ F x = q ∧
        kappa * (⟪(u : E3), j q⟫_ℝ - s) = ‖x‖ ^ 2 - rho ^ 2 ∧
        (q ∈ nativeRest ↔ rho ≤ ‖x‖) ∧
        (q ∈ nativeSeam ↔ ‖x‖ = rho) := by
    obtain ⟨v, hv, rfl⟩ := hq
    have hvs : v ∈ F.source := hbs hv
    dsimp only
    rw [F.left_inv hvs]
    have hcore : F v ∈ S.sourceCore i := hbufferCore ⟨v, ball_subset_closedBall hv, rfl⟩
    have hball : F v ∈ F '' ball (0 : E2) rho ↔ ‖v‖ < rho := by
      constructor
      · rintro ⟨x, hx, heq⟩
        have hxv := F.injOn (hsource (hsmall (ball_subset_closedBall hx))) hvs heq
        rw [← hxv]
        exact mem_ball_zero_iff.mp hx
      · intro hv'
        exact ⟨v, mem_ball_zero_iff.mpr hv', rfl⟩
    have hseam : F v ∈ nativeSeam ↔ ‖v‖ = rho := by
      constructor
      · rintro ⟨x, hx, heq⟩
        have hxv := F.injOn (hsource (hsmall (sphere_subset_closedBall hx))) hvs heq
        rw [← hxv]
        exact mem_sphere_zero_iff_norm.mp hx
      · intro hv'
        exact ⟨v, mem_sphere_zero_iff_norm.mpr hv', rfl⟩
    have hsigned : kappa * (⟪(u : E3), j (F v)⟫_ℝ - s) = ‖v‖ ^ 2 - rho ^ 2 := by
      change kappa * (⟪(u : E3), psi i (F v, 0)⟫_ℝ - s) = _
      rw [hform v (ball_subset_closedBall hv)]
      calc
        _ = kappa ^ 2 * (‖v‖ ^ 2 - rho ^ 2) := by dsimp only [s]; ring
        _ = _ := by rw [hkap2, one_mul]
    refine ⟨hvs, mem_ball_zero_iff.mp hv, rfl, hsigned, ?_, hseam⟩
    exact ⟨fun hh => le_of_not_gt (fun ht => hh.2 (hball.mpr ht)),
      fun hh => ⟨hcore, fun ht => (not_lt_of_ge hh) (hball.mp ht)⟩⟩
  have hjinj : Function.Injective j := by
    intro q q' hqq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hqq)
  have hrestq (q : UnitTwoSphere) : j q ∈ rest ↔ q ∈ nativeRest := by
    change j q ∈ j '' S.sourceCore i \ j '' (F '' ball (0 : E2) rho) ↔ _
    rw [← image_sdiff hjinj, hjinj.mem_set_image]
  have hseamq (q : UnitTwoSphere) : j q ∈ seam ↔ q ∈ nativeSeam :=
    hjinj.mem_set_image
  obtain ⟨E, hEf, hEs, hEt, _hEi⟩ := exists_collar_chart (psi i) (S.embedding i)
  have hEs0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ E.source := by
    rw [hEs]
    exact ⟨mem_univ _, by norm_num⟩
  have hEval (q : UnitTwoSphere) : E (q, 0) = j q := congrFun hEf (q, 0)
  have hEt0 (q : UnitTwoSphere) : j q ∈ E.target := by
    rw [← hEval]
    exact E.map_source (hEs0 q)
  have hEinv (q : UnitTwoSphere) : E.symm (j q) = (q, 0) := by
    rw [← hEval]
    exact E.left_inv (hEs0 q)
  let O := E.target ∩ E.symm ⁻¹' (W ×ˢ (univ : Set ℝ))
  have hO : IsOpen O := E.symm.continuousOn.isOpen_inter_preimage E.open_target
    (hW.prod isOpen_univ)
  have hOq (q : UnitTwoSphere) (hq : j q ∈ O) : q ∈ W := by
    have hh : E.symm (j q) ∈ W ×ˢ (univ : Set ℝ) := hq.2
    rw [hEinv] at hh
    exact hh.1
  refine ⟨hW, hqW, hWt, hWform, O, hO, ?_, fun _ hy => hEt ▸ hy.1, hOq, ?_⟩
  · refine ⟨hEt0 q0, ?_⟩
    change E.symm (j q0) ∈ W ×ˢ (univ : Set ℝ)
    rw [hEinv]
    exact ⟨hqW, mem_univ _⟩
  · rintro y hy ⟨q, rfl⟩
    obtain ⟨_hx, _hxnorm, _hinv, hsigned, hcore, hseam⟩ := hWform q (hOq q hy)
    constructor
    · rw [hrestq, hcore, hsigned]
      exact ⟨fun hh => sub_nonneg.mpr ((sq_le_sq₀ hrho.le (norm_nonneg _)).mpr hh),
        fun hh => (sq_le_sq₀ hrho.le (norm_nonneg _)).mp (sub_nonneg.mp hh)⟩
    · rw [hseamq, hseam]
      constructor
      · intro hh
        have hz : kappa * (⟪(u : E3), j q⟫_ℝ - s) = 0 := by
          rw [hsigned, hh, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hkap)
      · intro hh
        rw [hh, sub_self, mul_zero] at hsigned
        nlinarith only [hsigned, hrho, norm_nonneg (F.symm q)]

end PoincareConjecture.M25.Topology3D
