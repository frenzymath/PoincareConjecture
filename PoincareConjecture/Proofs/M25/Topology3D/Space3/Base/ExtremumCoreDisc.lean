import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreProtection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProduct
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem nativeDiscChart_geometry
    (F : OpenPartialHomeomorph E2 UnitTwoSphere)
    (rho : ℝ) (hrho : 0 < rho)
    (hsource : closedBall (0 : E2) rho ⊆ F.source) :
    let nativeDisc := F '' closedBall (0 : E2) rho
    let nativeOpen := F '' ball (0 : E2) rho
    let nativeSeam := F '' sphere (0 : E2) rho
    F 0 ∈ nativeOpen ∧ nativeOpen ⊆ nativeDisc ∧
      nativeDisc ⊆ F.target ∧
      IsOpen nativeOpen ∧ IsCompact nativeDisc ∧
      IsCompact nativeSeam ∧ IsConnected nativeSeam ∧
      closure nativeOpen = nativeDisc ∧
      nativeDisc \ nativeOpen = nativeSeam ∧
      frontier nativeOpen = nativeSeam := by
  have hopen : IsOpen (F '' ball (0 : E2) rho) :=
    F.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsource)
  have hcompact : IsCompact (F '' closedBall (0 : E2) rho) :=
    (isCompact_closedBall (0 : E2) rho).image_of_continuousOn (F.continuousOn.mono hsource)
  have hseamCompact : IsCompact (F '' sphere (0 : E2) rho) :=
    (isCompact_sphere (0 : E2) rho).image_of_continuousOn
      (F.continuousOn.mono (sphere_subset_closedBall.trans hsource))
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  have hconnected : IsConnected (F '' sphere (0 : E2) rho) :=
    (isConnected_sphere hdim (0 : E2) hrho.le).image F
      (F.continuousOn.mono (sphere_subset_closedBall.trans hsource))
  have hclosure : closure (F '' ball (0 : E2) rho) = F '' closedBall (0 : E2) rho := by
    apply subset_antisymm
    · exact closure_minimal (image_mono ball_subset_closedBall) hcompact.isClosed
    · rintro _ ⟨x, hx, rfl⟩
      apply mem_closure_image (F.continuousAt (hsource hx))
      rwa [closure_ball (0 : E2) hrho.ne']
  have hdiff : (F '' closedBall (0 : E2) rho) \ (F '' ball (0 : E2) rho) =
      F '' sphere (0 : E2) rho := by
    ext p
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
      refine ⟨x, mem_sphere_zero_iff_norm.mpr ?_, rfl⟩
      apply le_antisymm (mem_closedBall_zero_iff.mp hx)
      by_contra hn
      exact hnot ⟨x, mem_ball_zero_iff.mpr (lt_of_not_ge hn), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, sphere_subset_closedBall hx, rfl⟩, ?_⟩
      rintro ⟨y, hy, heq⟩
      have hyx : y = x := F.injOn (hsource (ball_subset_closedBall hy))
        (hsource (sphere_subset_closedBall hx)) heq
      have hylt := mem_ball_zero_iff.mp hy
      rw [hyx, mem_sphere_zero_iff_norm.mp hx] at hylt
      exact (lt_irrefl rho) hylt
  refine ⟨⟨0, mem_ball_self hrho, rfl⟩, image_mono ball_subset_closedBall,
    ?_, hopen, hcompact, hseamCompact, hconnected, hclosure, hdiff, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact F.map_source (hsource hx)
  · rw [hopen.frontier_eq, hclosure, hdiff]

theorem FamilySourceAtlas.exists_extremum_core_disc
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (atlas : FamilySourceAtlas original S)
    (horiginal : IsCollarEmbedding original)
    (hgap : ∀ k : Fin r, ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) p = 0 →
      4 * D < |⟪(u : E3), original (p, 0)⟫_ℝ - cut k|)
    (i : Fin n) (q : UnitTwoSphere) (hqCore : q ∈ S.sourceCore i)
    (hqCritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hqe : q ∈ e.source) (heq : e q = 0)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (kappa : ℝ) (hkappa : |kappa| = 1)
    (hform : ∀ p ∈ e.source, ⟪(u : E3), psi i (p, 0)⟫_ℝ =
      ⟪(u : E3), psi i (q, 0)⟫_ℝ +
        kappa * ((e p).1 ^ 2 + (e p).2 ^ 2))
    (d : ℝ) (hd : 0 < d) :
    let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    let F : OpenPartialHomeomorph E2 UnitTwoSphere :=
      L.toHomeomorph.transOpenPartialHomeomorph e.symm
    let j : UnitTwoSphere → E3 := fun p => psi i (p, 0)
    let c := ⟪(u : E3), j q⟫_ℝ
    let W : Set E3 :=
      {y | ∀ k : Fin r, 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|}
    let U : Set UnitTwoSphere := (atlas.chart i).source ∩ j ⁻¹' W
    F.source = L ⁻¹' e.target ∧ F.target = e.source ∧ F 0 = q ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ F.symm F.target ∧
      IsOpen U ∧ q ∈ U ∧ U ⊆ S.sourceCore i ∧
      ∃ rho : ℝ, 0 < rho ∧ rho < d ∧
        closedBall (0 : E2) (2 * rho) ⊆ F.source ∧
        F '' closedBall (0 : E2) (2 * rho) ⊆ U ∧
        ∃ G : OpenPartialHomeomorph (E2 × ℝ) E3,
          (0, c) ∈ G.source ∧ G (0, c) = j q ∧
          ContDiffOn ℝ ∞ G G.source ∧
          ContDiffOn ℝ ∞ G.symm G.target ∧ G.target ⊆ W ∧
          closedBall (0 : E2) (2 * rho) ×ˢ
            Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ G.source ∧
          (∀ p ∈ G.source,
            L p.1 ∈ e.target ∧ F p.1 ∈ U ∧
            G p = (heightPlaneCoordinates u).symm
              ((heightPlaneCoordinates u (j (F p.1))).1, p.2) ∧
            ⟪(u : E3), G p⟫_ℝ = p.2 ∧
            (G p ∈ range j ↔ p.2 = c + kappa * ‖p.1‖ ^ 2)) ∧
          (∀ x ∈ closedBall (0 : E2) (2 * rho),
            G (x, c + kappa * ‖x‖ ^ 2) = j (F x) ∧
            j (F x) ∈ G.target ∧
            G.symm (j (F x)) = (x, c + kappa * ‖x‖ ^ 2) ∧
            ⟪(u : E3), j (F x)⟫_ℝ = c + kappa * ‖x‖ ^ 2) ∧
          let nativeDisc := F '' closedBall (0 : E2) rho
          let nativeOpen := F '' ball (0 : E2) rho
          let nativeSeam := F '' sphere (0 : E2) rho
          let disc := j '' nativeDisc
          let seam := j '' nativeSeam
          q ∈ nativeOpen ∧ IsOpen nativeOpen ∧
            IsCompact nativeDisc ∧ IsCompact nativeSeam ∧
            IsConnected nativeSeam ∧
            closure nativeOpen = nativeDisc ∧
            nativeDisc \ nativeOpen = nativeSeam ∧
            frontier nativeOpen = nativeSeam ∧
            nativeDisc ⊆ S.sourceCore i ∧
            IsCompact disc ∧ IsCompact seam ∧ IsConnected seam ∧
            disc ⊆ G.target ∧
            (∀ a : Fin S.capCount, Disjoint disc (S.cap a).cap) ∧
            disc \ (j '' nativeOpen) = seam ∧
            (∀ p ∈ nativeSeam,
              ⟪(u : E3), j p⟫_ℝ = c + kappa * rho ^ 2) ∧
            ∀ p ∈ nativeOpen \ {q},
              0 < kappa * (⟪(u : E3), j p⟫_ℝ - c) ∧
                kappa * (⟪(u : E3), j p⟫_ℝ - c) < rho ^ 2 := by
  let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let F : OpenPartialHomeomorph E2 UnitTwoSphere :=
    L.toHomeomorph.transOpenPartialHomeomorph e.symm
  let j : UnitTwoSphere → E3 := fun p => psi i (p, 0)
  let c := ⟪(u : E3), j q⟫_ℝ
  let W : Set E3 :=
    {y | ∀ k : Fin r, 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|}
  let U : Set UnitTwoSphere := (atlas.chart i).source ∩ j ⁻¹' W
  obtain ⟨hW, hU, hqU, hUcore, havoid⟩ :=
    atlas.critical_protected_neighborhood horiginal hgap i q hqCore hqCritical
  have hFsource : F.source = L ⁻¹' e.target := rfl
  have hFtarget : F.target = e.source := rfl
  have hFzero : F 0 = q := by
    change e.symm (L 0) = q
    rw [map_zero, ← heq, e.left_inv hqe]
  have hFs : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ F F.source :=
    hei.comp L.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  have hFi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ F.symm F.target :=
    L.symm.contDiff.contMDiff.comp_contMDiffOn he
  obtain ⟨rho0, hrho0, _hrho0d, G0, h0G0, hG0zero, hG0s, hG0i, _hprod0,
    hG0form, hG0graph⟩ := exists_stackMorseProduct (psi i) (S.embedding i) u q hqCritical
      e hqe heq he hei kappa hkappa hform U hU hqU d hd
  let V := G0.source ∩ G0 ⁻¹' W
  have hV : IsOpen V := G0.isOpen_inter_preimage hW
  let G := G0.restrOpen V hV
  have h0G : (0, c) ∈ G.source := by
    refine ⟨h0G0, h0G0, ?_⟩
    change G0 (0, c) ∈ W
    rw [hG0zero]
    exact hqU.2
  have hGs : ContDiffOn ℝ ∞ G G.source := hG0s.mono inter_subset_left
  have hGi : ContDiffOn ℝ ∞ G.symm G.target := hG0i.mono inter_subset_left
  have hGW : G.target ⊆ W := by
    intro y hy
    have hs := G.map_target hy
    have hw : G (G.symm y) ∈ W := hs.2.2
    rwa [G.right_inv hy] at hw
  obtain ⟨eps, heps, hepsG⟩ := Metric.isOpen_iff.mp G.open_source (0, c) h0G
  obtain ⟨rho, hrho, hrbound⟩ := exists_between
    (show (0 : ℝ) < min rho0 (min d (min 1 (eps / 8))) from
      lt_min hrho0 (lt_min hd (lt_min zero_lt_one (div_pos heps (by norm_num)))))
  have hrr : rho < rho0 := hrbound.trans_le (min_le_left _ _)
  have hrd : rho < d := hrbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrsmall : rho < min 1 (eps / 8) :=
    hrbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hr1 : rho < 1 := hrsmall.trans_le (min_le_left _ _)
  have hre : rho < eps / 8 := hrsmall.trans_le (min_le_right _ _)
  have hr2 : 2 * rho < eps := by linarith only [hre, hrho]
  have hr4 : 4 * rho ^ 2 < eps := by nlinarith only [hrho, hr1, hre]
  have hprod : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ G.source := by
    intro p hp
    apply hepsG
    rw [mem_ball, Prod.dist_eq, dist_zero_right, Real.dist_eq]
    refine max_lt ((mem_closedBall_zero_iff.mp hp.1).trans_lt hr2) ?_
    exact abs_lt.mpr ⟨by linarith only [hp.2.1, hr4], by linarith only [hp.2.2, hr4]⟩
  have hGform (p : E2 × ℝ) (hp : p ∈ G.source) :
      L p.1 ∈ e.target ∧ F p.1 ∈ U ∧
      G p = (heightPlaneCoordinates u).symm
        ((heightPlaneCoordinates u (j (F p.1))).1, p.2) ∧
      ⟪(u : E3), G p⟫_ℝ = p.2 ∧
      (G p ∈ range j ↔ p.2 = c + kappa * ‖p.1‖ ^ 2) := hG0form p hp.1
  have hbuffer (x : E2) (hx : x ∈ closedBall (0 : E2) (2 * rho)) :
      x ∈ F.source ∧ F x ∈ U := by
    have hxc : (x, c) ∈ G.source :=
      hprod ⟨hx, by constructor <;> nlinarith only [sq_nonneg rho]⟩
    exact ⟨(hGform _ hxc).1, (hGform _ hxc).2.1⟩
  have hsource : closedBall (0 : E2) (2 * rho) ⊆ F.source := fun x hx => (hbuffer x hx).1
  have hbufferU : F '' closedBall (0 : E2) (2 * rho) ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hbuffer x hx).2
  have hgraph (x : E2) (hx : x ∈ closedBall (0 : E2) (2 * rho)) :
      G (x, c + kappa * ‖x‖ ^ 2) = j (F x) ∧
      j (F x) ∈ G.target ∧
      G.symm (j (F x)) = (x, c + kappa * ‖x‖ ^ 2) ∧
      ⟪(u : E3), j (F x)⟫_ℝ = c + kappa * ‖x‖ ^ 2 := by
    have hxb : ‖x‖ ^ 2 ≤ 4 * rho ^ 2 := by
      nlinarith only [mem_closedBall_zero_iff.mp hx, norm_nonneg x]
    have hkap := abs_le.mp hkappa.le
    have ht : c + kappa * ‖x‖ ^ 2 ∈ Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) := by
      have hl := mul_le_mul_of_nonneg_right hkap.1 (sq_nonneg ‖x‖)
      have hu := mul_le_mul_of_nonneg_right hkap.2 (sq_nonneg ‖x‖)
      constructor <;> nlinarith only [hl, hu, hxb]
    have hp : (x, c + kappa * ‖x‖ ^ 2) ∈ G.source := hprod ⟨hx, ht⟩
    have hequal : G (x, c + kappa * ‖x‖ ^ 2) = j (F x) :=
      hG0graph x (closedBall_subset_closedBall (by linarith only [hrr]) hx)
    have htarget : j (F x) ∈ G.target := by
      rw [← hequal]
      exact G.map_source hp
    refine ⟨hequal, htarget, ?_, ?_⟩
    · rw [← hequal]
      exact G.left_inv hp
    · rw [← hequal]
      exact (hGform _ hp).2.2.2.1
  have hrsub : closedBall (0 : E2) rho ⊆ closedBall (0 : E2) (2 * rho) :=
    closedBall_subset_closedBall (by linarith only [hrho])
  obtain ⟨hzeroOpen, _hopenDisc, _hdiscTarget, hopen, hcompact, hseamCompact,
    hconnected, hclosure, hdiff, hfrontier⟩ :=
    nativeDiscChart_geometry F rho hrho (hrsub.trans hsource)
  have hj : Continuous j := (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hjinj : Function.Injective j := by
    intro p p' hpp
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hpp)
  have hdiscTarget : j '' (F '' closedBall (0 : E2) rho) ⊆ G.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (hgraph x (hrsub hx)).2.1
  refine ⟨hFsource, hFtarget, hFzero, hFs, hFi, hU, hqU, hUcore,
    rho, hrho, hrd, hsource, hbufferU, G, h0G, hG0zero, hGs, hGi, hGW, hprod,
    hGform, hgraph, ?_⟩
  refine ⟨hFzero ▸ hzeroOpen, hopen, hcompact, hseamCompact, hconnected,
    hclosure, hdiff, hfrontier, ?_, hcompact.image_of_continuousOn hj.continuousOn,
    hseamCompact.image_of_continuousOn hj.continuousOn,
    hconnected.image j hj.continuousOn, hdiscTarget, ?_, ?_, ?_, ?_⟩
  · exact (image_mono hrsub).trans (hbufferU.trans hUcore)
  · intro a
    exact (havoid a).mono_left (hdiscTarget.trans hGW)
  · rw [← image_sdiff hjinj, hdiff]
  · rintro _ ⟨x, hx, rfl⟩
    rw [(hgraph x (hrsub (sphere_subset_closedBall hx))).2.2.2,
      mem_sphere_zero_iff_norm.mp hx]
  · rintro p ⟨⟨x, hx, rfl⟩, hnot⟩
    have hxne : x ≠ 0 := by
      intro hxzero
      apply hnot
      simpa only [hxzero, hFzero, mem_singleton_iff]
    have hheight := (hgraph x (hrsub (ball_subset_closedBall hx))).2.2.2
    have hkap2 : kappa ^ 2 = 1 := by nlinarith only [sq_abs kappa, hkappa]
    have hsigned : kappa * (⟪(u : E3), j (F x)⟫_ℝ - c) = ‖x‖ ^ 2 := by
      rw [hheight]
      nlinarith only [hkap2]
    rw [hsigned]
    exact ⟨sq_pos_of_pos (norm_pos_iff.mpr hxne),
      (sq_lt_sq₀ (norm_nonneg x) hrho.le).mpr (mem_ball_zero_iff.mp hx)⟩

end PoincareConjecture.M25.Topology3D
