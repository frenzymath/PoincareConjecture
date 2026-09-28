import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumBandCaller
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMixedBall









set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilySourceAtlas.exists_ball_of_extremum_core
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (atlas : FamilySourceAtlas original S)
    (hP : PlanarSchoenfliesService)
    (horiginal : IsCollarEmbedding original)
    (hgap : ∀ k : Fin r, ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) p = 0 →
      4 * D < |⟪(u : E3), original (p, 0)⟫_ℝ - cut k|)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (i : Fin n)
    (hterminal :
      (S.sourceCore i ∩ {p : UnitTwoSphere |
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p = 0}).Subsingleton)
    (q : UnitTwoSphere) (hqCore : q ∈ S.sourceCore i)
    (hqCritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0)
    (sigma tau : ℝ)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hsigma : sigma * sigma = 1) (htau : tau * tau = 1)
    (hdefinite : sigma = tau)
    (hqe : q ∈ e.source) (heq : e q = 0)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ p ∈ e.source, ⟪(u : E3), psi i (p, 0)⟫_ℝ =
      ⟪(u : E3), psi i (q, 0)⟫_ℝ +
        sigma * (e p).1 ^ 2 + tau * (e p).2 ^ 2) :
    ∃ Q : BallNeighborhoodChart E3 E3,
      Q.boundary = range (fun p : UnitTwoSphere => psi i (p, 0)) ∧
      Q.boundary = psi i '' ((univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ)) := by
  have hcases : sigma = 1 ∨ sigma = -1 := by
    have hprod : (sigma - 1) * (sigma + 1) = 0 := by nlinarith only [hsigma]
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (by linarith only [h])
    · exact Or.inr (by linarith only [h])
  have hkappa : |sigma| = 1 := by
    rw [hdefinite]
    have hh : |tau| * |tau| = 1 := by rw [← abs_mul, htau, abs_one]
    nlinarith only [hh, abs_nonneg tau]
  have hdefiniteForm : ∀ p ∈ e.source, ⟪(u : E3), psi i (p, 0)⟫_ℝ =
      ⟪(u : E3), psi i (q, 0)⟫_ℝ + sigma * ((e p).1 ^ 2 + (e p).2 ^ 2) := by
    intro p hp
    rw [hform p hp, ← hdefinite]
    ring
  let L : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let F : OpenPartialHomeomorph E2 UnitTwoSphere :=
    L.toHomeomorph.transOpenPartialHomeomorph e.symm
  let j : UnitTwoSphere → E3 := fun p => psi i (p, 0)
  let c : ℝ := ⟪(u : E3), j q⟫_ℝ
  obtain ⟨_hFs, _hFt, _hFzero, _hF, _hFi, _hW, _hU, _hqU, _hUcore, _hAvoid,
      rho, hrho, _hrbound, _hrsmall, _hFsource, _hFbuffer, A, _hA0, _hAq,
      hA, hAi, _hAt, hAsource, hAform, _hAgraph, hgeometry⟩ :=
    atlas.exists_extremum_band horiginal hgap hzero i hterminal q hqCore hqCritical
      e hqe heq he hei sigma hkappa hdefiniteForm 1 zero_lt_one
  let discOpen : Set E3 := j '' (F '' ball (0 : E2) rho)
  let K : Set E3 := S.retainedCore i \ discOpen
  let morse : E2 → E3 := fun x => A (x, c + sigma * ‖x‖ ^ 2)
  let s : ℝ := c + sigma * rho ^ 2
  obtain ⟨_hqOpen, _hOpen, _hNativeCompact, _hNativeSeamCompact, _hNativeConnected,
      _hClosure, _hNativeDiff, _hFrontier, _hDiscCore, _hDiscCompact, _hSeamCompact,
      _hSeamConnected, _hDiscTarget, _hDiscAvoid, _hDiscDiff, _hDiscImage,
      hOpenImage, _hSeamImage, _hSeamHeight, _hBounds, a, ha, hSign,
      _hOwner, _hCard, hOrder, hPositive, hNegative, _hImage, hCompact,
      _hConnected, _hNativeRegular, hBand, _hRegular, _hNewLevel, _hOldLevel,
      _hCover, _hNew, _hOld, hWholeDiff, eta, heta, gamma, hGamma,
      hEmbedding, hLevels⟩ := hgeometry
  let C : SurgeryCapTag (psi i) u :=
    Eq.mp (congrArg (fun k : Fin n => SurgeryCapTag (psi k) u) ha) (S.cap a)
  have htransport (j k : Fin n) (h : j = k) (C0 : SurgeryCapTag (psi j) u) :
      let C1 := Eq.mp (congrArg (fun l : Fin n => SurgeryCapTag (psi l) u) h) C0
      C1.sign = C0.sign ∧ C1.cutHeight = C0.cutHeight ∧
        C1.removal = C0.removal ∧ C1.cap = C0.cap ∧ C1.seam = C0.seam := by
    subst k
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hC : C.sign = (S.cap a).sign ∧ C.cutHeight = (S.cap a).cutHeight ∧
      C.removal = (S.cap a).removal ∧ C.cap = (S.cap a).cap ∧
      C.seam = (S.cap a).seam := htransport _ _ ha (S.cap a)
  obtain ⟨hCs, hCc, hCr, hCcap, _hCseam⟩ := hC
  let t0 : ℝ := (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  have hCheight : C.cutHeight + C.sign * C.removal = t0 := by
    rw [hCc, hCs, hCr]
  have horder : 0 < sigma * (t0 - s) := by
    rcases hcases with hk | hk
    · obtain ⟨hl, hu⟩ := hPositive hk
      rw [hl, hu] at hOrder
      rw [hk, one_mul]
      exact sub_pos.mpr hOrder
    · obtain ⟨hl, hu⟩ := hNegative hk
      rw [hl, hu] at hOrder
      rw [hk, neg_one_mul]
      linarith only [hOrder]
  refine exists_ball_of_morse_disc_and_saved_cap hP (psi i) (S.embedding i) u C A hA hAi
    c sigma rho hkappa hrho (hCs.trans hSign) hAsource
    (fun p hp => (hAform p hp).2.2.2.1) (fun p hp => (hAform p hp).2.2.2.2)
    K hCompact ?_ ?_ ?_ eta heta gamma hGamma ?_ ?_
  · change 0 < sigma * ((C.cutHeight + C.sign * C.removal) - s)
    rw [hCheight]
    exact horder
  · change K = {y : E3 | y ∈ range j ∧ ⟪(u : E3), y⟫_ℝ ∈
      Icc (min s (C.cutHeight + C.sign * C.removal))
        (max s (C.cutHeight + C.sign * C.removal))}
    rw [hCheight]
    exact hBand
  · change range j \ (morse '' ball (0 : E2) rho) = K ∪ C.cap
    change discOpen = morse '' ball (0 : E2) rho at hOpenImage
    rw [← hOpenImage, hCcap]
    exact hWholeDiff
  · intro z hz
    apply hEmbedding z
    change z ∈ Icc (min s (C.cutHeight + C.sign * C.removal) - eta)
      (max s (C.cutHeight + C.sign * C.removal) + eta) at hz
    rw [hCheight] at hz
    exact hz
  · intro z hz
    apply hLevels z
    change z ∈ Icc (min s (C.cutHeight + C.sign * C.removal) - eta)
      (max s (C.cutHeight + C.sign * C.removal) + eta) at hz
    rw [hCheight] at hz
    exact hz

end PoincareConjecture.M25.Topology3D
