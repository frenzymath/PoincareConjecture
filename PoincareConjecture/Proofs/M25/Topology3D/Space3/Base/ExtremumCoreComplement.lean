import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutSides
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.seam_height_gaps_of_buffer_avoidance
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (i : Fin n) (q : UnitTwoSphere)
    (hgap : ∀ k : Fin r, 4 * D < |⟪(u : E3), psi i (q, 0)⟫_ℝ - cut k|) :
    let c := ⟪(u : E3), psi i (q, 0)⟫_ℝ
    (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal + 3 * D < c) ∧
    (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
      c + 3 * D < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) := by
  constructor
  · intro a ha hs
    have hside : (S.cap a).cutHeight < ⟪(u : E3), psi i (q, 0)⟫_ℝ := by
      rcases S.cap_points_on_birth_side a (hzero (S.birth a)) with h | h
      · simpa only [ha] using h.2 q
      · have hsign := h.1
        rw [hs] at hsign
        norm_num at hsign
    have hg := hgap (S.birth a)
    rw [← S.cap_cut a, abs_of_pos (sub_pos.mpr hside)] at hg
    simp only [hs, one_mul]
    linarith only [hg, S.cap_removal a]
  · intro a ha hs
    have hside : ⟪(u : E3), psi i (q, 0)⟫_ℝ < (S.cap a).cutHeight := by
      rcases S.cap_points_on_birth_side a (hzero (S.birth a)) with h | h
      · have hsign := h.1
        rw [hs] at hsign
        norm_num at hsign
      · simpa only [ha] using h.2 q
    have hg := hgap (S.birth a)
    rw [← S.cap_cut a, abs_of_neg (sub_neg.mpr hside)] at hg
    simp only [hs, neg_one_mul]
    linarith only [hg, S.cap_removal a]


theorem FamilyCutState.morse_disc_complement_geometry
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
    (hdisc : F '' closedBall (0 : E2) rho ⊆ S.sourceCore i)
    (havoid : ∀ a : Fin S.capCount,
      Disjoint ((fun q : UnitTwoSphere => psi i (q, 0)) ''
        (F '' closedBall (0 : E2) rho)) (S.cap a).cap)
    (hunique : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0 →
          q = F 0) :
    let nativeDisc : Set UnitTwoSphere := F '' closedBall (0 : E2) rho
    let nativeOpen : Set UnitTwoSphere := F '' ball (0 : E2) rho
    let nativeSeam : Set UnitTwoSphere := F '' sphere (0 : E2) rho
    let nativeRest : Set UnitTwoSphere := S.sourceCore i \ nativeOpen
    let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
    let L : Set E3 := j '' nativeRest
    IsCompact nativeRest ∧ IsConnected nativeRest ∧
      F 0 ∉ nativeRest ∧
      (∀ q ∈ nativeRest,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) ∧
      nativeDisc ∩ nativeRest = nativeSeam ∧
      L = S.retainedCore i \ j '' nativeOpen ∧
      IsCompact L ∧ IsConnected L ∧
      range j = (L ∪ j '' nativeDisc) ∪
        (⋃ a : {a : Fin S.capCount // S.owner a = i}, (S.cap a.1).cap) ∧
      L ∩ (j '' nativeDisc) = j '' nativeSeam ∧
      (∀ a : Fin S.capCount, S.owner a = i → L ∩ (S.cap a).cap = (S.cap a).seam) ∧
      (∀ a : Fin S.capCount, Disjoint (j '' nativeDisc) (S.cap a).cap) := by
  let nativeDisc : Set UnitTwoSphere := F '' closedBall (0 : E2) rho
  let nativeOpen : Set UnitTwoSphere := F '' ball (0 : E2) rho
  let nativeSeam : Set UnitTwoSphere := F '' sphere (0 : E2) rho
  let nativeRest : Set UnitTwoSphere := S.sourceCore i \ nativeOpen
  let j : UnitTwoSphere → E3 := fun q => psi i (q, 0)
  let L : Set E3 := j '' nativeRest
  obtain ⟨hzero, hOD, _hDt, hO, hD, _hSc, hSn, _hclosure, hdiff, _hfrontier⟩ :=
    nativeDiscChart_geometry F rho hrho hsource
  obtain ⟨hKc, hKn⟩ := S.sourceCore_compact_connected i
  have hseam : IsConnected (nativeDisc \ nativeOpen) := by
    simpa only [nativeDisc, nativeOpen, hdiff] using hSn
  obtain ⟨hRc, hRn, hintersection⟩ :=
    compact_connected_diff_of_connected_seam hKc hKn hD hdisc hO hOD hseam
  have hnot : F 0 ∉ nativeRest := fun h => h.2 hzero
  have hregular : ∀ q ∈ nativeRest,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0 := by
    intro q hq heq
    exact hnot ((hunique q hq.1 heq) ▸ hq)
  have hnative : nativeDisc ∩ nativeRest = nativeSeam :=
    hintersection.trans hdiff
  have hj : Continuous j :=
    (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hinj : Function.Injective j := by
    intro q q' hq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hq)
  have hLdiff : L = S.retainedCore i \ j '' nativeOpen :=
    image_sdiff hinj (S.sourceCore i) nativeOpen
  have hunion : S.sourceCore i = nativeRest ∪ nativeDisc := by
    ext q
    constructor
    · intro hq
      by_cases hqO : q ∈ nativeOpen
      · exact Or.inr (hOD hqO)
      · exact Or.inl ⟨hq, hqO⟩
    · rintro (hq | hq)
      · exact hq.1
      · exact hdisc hq
  have himage : S.retainedCore i = L ∪ j '' nativeDisc := by
    change j '' S.sourceCore i = _
    rw [hunion, image_union]
  obtain ⟨_hCc, _hCn, _hCdiff, hcover, hcaps⟩ := S.retainedCore_geometry i
  have hcover' : range j = (L ∪ j '' nativeDisc) ∪
      (⋃ a : {a : Fin S.capCount // S.owner a = i}, (S.cap a.1).cap) := by
    rw [← himage]
    exact hcover
  have hnew : L ∩ (j '' nativeDisc) = j '' nativeSeam := by
    change (j '' nativeRest) ∩ (j '' nativeDisc) = _
    rw [← image_inter hinj, inter_comm, hnative]
  refine ⟨hRc, hRn, hnot, hregular, hnative, hLdiff,
    hRc.image hj, hRn.image j hj.continuousOn, hcover', hnew, ?_, havoid⟩
  intro a ha
  ext y
  constructor
  · intro hy
    change y ∈ L ∩ (S.cap a).cap at hy
    apply (hcaps a ha).le
    refine ⟨?_, hy.2⟩
    rw [hLdiff] at hy
    exact hy.1.1
  · intro hy
    have hKcap := (hcaps a ha).ge hy
    refine ⟨?_, hKcap.2⟩
    change y ∈ L
    rw [hLdiff]
    refine ⟨hKcap.1, ?_⟩
    intro hOpen
    exact disjoint_left.mp (havoid a) (image_mono hOD hOpen) hKcap.2

end PoincareConjecture.M25.Topology3D
