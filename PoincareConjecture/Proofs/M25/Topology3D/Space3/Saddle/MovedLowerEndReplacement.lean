import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerCutMotion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedLowerEndLaterScales
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthCapEndTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_moved_lower_end_replacement
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (P : SurgeryCapProfile) (z tau : ℝ)
    (hz : W.level < z)
    (hzc : z < ⟪(u : E3), psi (D.point, 0)⟫_ℝ) (htau : 0 < tau) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (psi (D.point, 0))
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    let R : Set E3 := S ∩ {y | z ≤ H y}
    ∃ (b : ℝ) (T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
      (V : Fin 2 → Set E3),
      0 < b ∧ 4 * b < tau ∧ 4 * b < c - z ∧
      (∀ i : Fin 2,
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
        ContDiffOn ℝ ∞ (T i) (T i).source ∧
        ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
        (∀ p ∈ (T i).source, H (T i p) = p.2) ∧
        (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
        IsOpen (V i) ∧
        T i '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 4 * b) (z + 4 * b)) ⊆ V i) ∧
      Disjoint (V 0) (V 1) ∧
      (∀ t ∈ Icc (z - 4 * b) (z + 4 * b),
        S ∩ {y : E3 | H y = t} =
          ⋃ i : Fin 2, T i '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
      ∀ lambda : Fin 2 → ℝ, (∀ i, 0 < lambda i) →
        (∀ i, lambda i * P.heightBound < b) →
        let south : Fin 2 → Set E3 := fun i =>
          P.capMap (T i) z 1 0 (lambda i) ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
        ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          G '' S = R ∪ south 0 ∪ south 1 ∧
          G.symm '' (R ∪ south 0 ∪ south 1) = S ∧
          (∀ (i : Fin 2) (y : E3), y ∈ south i →
            |H y - z| ≤ lambda i * P.heightBound) ∧
          IsCollarEmbedding (fun p => G (psi p)) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (psi (D.point, 0))
  let S : Set E3 := range j
  let R : Set E3 := S ∩ {y : E3 | z ≤ H y}
  let Rold : Set E3 := S ∩ {y : E3 | W.level ≤ H y}
  let ell : Fin 2 → ℝ := fun i =>
    (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal
  let E : Fin 2 → Set E3 := fun i => j ''
    ((D.cap (W.label i)).sourceCap ∪ W.leg i '' (univ ×ˢ Icc (ell i) W.level))
  obtain ⟨e, g, K, _C, he, _hbuffer, _hC, _hCV, _hg, _hgi, _hK, _hKi,
    _hmono, _hg0, _hK0, hHeight, _hMem, _hImage, _hgfixed, _hKfixed,
    _hgsupp, _hKsupp, _htrack, hAffine, hSets⟩ :=
    exists_saddle_lower_cut_motion psi hpsi u D W (W.level - 1) z
      (by linarith) hz hzc
  obtain ⟨_r, _gamma, _ov, _w, Told, _phase, d, Vold, hTold, hd, _hdtau,
    hBuffers, hVdis, hLevels, hCover, hRcompact, hLater⟩ :=
    exists_saddle_nonnested_lower_end_later_scales hP psi hpsi u D W
      hnonnested P tau htau
  change S = Rold ∪ E 0 ∪ E 1 at hCover
  have hOld (i : Fin 2) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (Told i).source ∧
      ContDiffOn ℝ ∞ (Told i) (Told i).source ∧
      ContDiffOn ℝ ∞ (Told i).symm (Told i).target ∧
      (∀ p ∈ (Told i).source, H (Told i p) = p.2) ∧
      (∀ y ∈ (Told i).target, ((Told i).symm y).2 = H y) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hs, hT, hTi, hh, hhi, _⟩ := hTold i
    exact ⟨hs, hT, hTi, hh, hhi⟩
  let b := min e (min d (min tau (c - z))) / 8
  have hm : 0 < min e (min d (min tau (c - z))) :=
    lt_min he (lt_min hd (lt_min htau (sub_pos.mpr hzc)))
  have hb : 0 < b := div_pos hm (by norm_num)
  have hbe : 4 * b < e := by
    have := min_le_left e (min d (min tau (c - z)))
    dsimp [b]
    linarith
  have hbd : 4 * b < d := by
    have := (min_le_right e (min d (min tau (c - z)))).trans
      (min_le_left d (min tau (c - z)))
    dsimp [b]
    linarith
  have hbt : 4 * b < tau := by
    have := ((min_le_right e (min d (min tau (c - z)))).trans
      (min_le_right d (min tau (c - z)))).trans (min_le_left tau (c - z))
    dsimp [b]
    linarith
  have hbc : 4 * b < c - z := by
    have := ((min_le_right e (min d (min tau (c - z)))).trans
      (min_le_right d (min tau (c - z)))).trans (min_le_right tau (c - z))
    dsimp [b]
    linarith
  let T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3 := fun i =>
    heightTransportTube (Told i) (g 1) (K 1)
  let V : Fin 2 → Set E3 := fun i => K 1 '' Vold i
  have hSource (i : Fin 2) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source :=
    heightTransportTube_closedDisc_source _ _ _ (hOld i).1
  have hTubeHeight (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ (T i).source) :
      H (T i p) = p.2 :=
    heightTransportTube_height _ _ _ u u (hOld i).2.2.2.1
      (fun y => (hHeight 1 y).1) p hp
  have hTubeInvHeight (i : Fin 2) (y : E3) (hy : y ∈ (T i).target) :
      ((T i).symm y).2 = H y := by
    change g 1 (((Told i).symm ((K 1).symm y)).2) = H y
    rw [(hOld i).2.2.2.2 _ ((heightTransportTube_mem_target _ _ _ y).mp hy),
      (hHeight 1 y).2, (g 1).apply_symm_apply]
  have hOffset (t : ℝ) (ht : t ∈ Icc (z - 4 * b) (z + 4 * b)) :
      |t - z| ≤ e ∧ W.level + (t - z) ∈
        Icc (W.level - 4 * d) (W.level + 4 * d) := by
    have hh : |t - z| ≤ 4 * b := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨hh.trans hbe.le, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hStack (i : Fin 2) :
      T i '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 4 * b) (z + 4 * b)) ⊆ V i := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hi : (g 1).symm t = W.level + (t - z) := by
      simpa only [add_sub_cancel] using (hAffine (t - z) (hOffset t ht).1).2
    change K 1 (Told i (x, (g 1).symm t)) ∈ K 1 '' Vold i
    refine ⟨Told i (x, (g 1).symm t), ?_, rfl⟩
    apply (hBuffers i).2.2.2
    exact ⟨(x, (g 1).symm t), ⟨hx, by rw [hi]; exact (hOffset t ht).2⟩, rfl⟩
  have hSlice (i : Fin 2) (X : Set E2) (t : ℝ) :
      K 1 '' (Told i '' (X ×ˢ ({t} : Set ℝ))) =
        T i '' (X ×ˢ ({g 1 t} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨v, ⟨⟨x, t'⟩, ⟨hx, ht'⟩, rfl⟩, rfl⟩
      have htt : t' = t := ht'
      subst t'
      exact ⟨(x, g 1 t), ⟨hx, rfl⟩,
        heightTransportTube_reparametrized_apply (Told i) (g 1) (K 1) (x, t)⟩
    · rintro ⟨⟨x, t'⟩, ⟨hx, ht'⟩, rfl⟩
      have htt : t' = g 1 t := ht'
      subst t'
      refine ⟨Told i (x, t), ⟨(x, t), ⟨hx, rfl⟩, rfl⟩, ?_⟩
      exact (heightTransportTube_reparametrized_apply (Told i) (g 1) (K 1) (x, t)).symm
  have hNewLevels (t : ℝ) (ht : t ∈ Icc (z - 4 * b) (z + 4 * b)) :
      S ∩ {y : E3 | H y = t} =
        ⋃ i : Fin 2, T i '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := by
    have hset := (hSets (t - z) (hOffset t ht).1).1
    have ha : g 1 (W.level + (t - z)) = t := by
      simpa only [add_sub_cancel] using (hAffine (t - z) (hOffset t ht).1).1
    have hset' : K 1 '' (S ∩ {y : E3 | H y = W.level + (t - z)}) =
        S ∩ {y : E3 | H y = t} := by simpa only [add_sub_cancel] using hset
    rw [← hset', hLevels _ (hOffset t ht).2, image_iUnion]
    apply iUnion_congr
    intro i
    rw [hSlice, ha]
  refine ⟨b, T, V, hb, hbt, hbc, ?_, ?_, hNewLevels, ?_⟩
  · intro i
    exact ⟨hSource i, heightTransportTube_contDiffOn _ _ _ (hOld i).2.1,
      heightTransportTube_contDiffOn_symm _ _ _ (hOld i).2.2.1,
      hTubeHeight i, hTubeInvHeight i,
      (K 1).toHomeomorph.isOpenMap _ (hBuffers i).2.2.1, hStack i⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨v, hv, hvy⟩
    have hxv := (K 1).injective (hxy.trans hvy.symm)
    exact Set.disjoint_left.mp hVdis hx (hxv.symm ▸ hv)
  intro lambda hlambda hlambdab
  have hlambdad (i : Fin 2) : lambda i * P.heightBound < d :=
    (hlambdab i).trans (by linarith)
  obtain ⟨Q, A, o, hA, hdis⟩ := hLater lambda hlambda hlambdad
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun t => (P.horizontal_pos t).ne') (fun x => (P.vertical_pos x).ne')
  let north : Fin 2 → Set E3 := fun i =>
    (fun q : UnitTwoSphere => Told i
      ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let southOld : Fin 2 → Set E3 := fun i =>
    (fun q : UnitTwoSphere => Told i
      ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let south : Fin 2 → Set E3 := fun i =>
    P.capMap (T i) z 1 0 (lambda i) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let other : Fin 2 → Fin 2 := ![1, 0]
  have hdisother (i : Fin 2) : Disjoint (A i).closedRegion (A (other i)).closedRegion := by
    fin_cases i
    · exact hdis
    · exact hdis.symm
  have hNs (i : Fin 2) : ∃ N : BallNeighborhoodChart E3 E3,
      N.boundary = southOld i ∪ north i ∧
      (∀ y : E3, N.chart y = Told i ((M (heightCoordinates y)).1,
        W.level + lambda i * (M (heightCoordinates y)).2)) ∧
      N.closedRegion ⊆ (A i).closedRegion ∧
      north i = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} ∧
      southOld i ∩ north i = Told i '' (sphere (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) := by
    obtain ⟨_ho, _ho1, hlt, hlg, _hchart, _hsource, _htarget, _hpoint,
      _hinv, hbdy, _hinside, _hregion, _hheight, hfill, _hcut, _hpatch,
      _havoid, _hret, _hrim⟩ := hA i
    have hfilled : ∀ t ∈ Icc (ell i) W.level,
        Told i '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ (A i).closedRegion := by
      intro t ht y hy
      exact ((hfill t ht).2.symm ▸ hy).1
    have hnorth : north i ⊆ (A i).closedRegion := by
      intro y hy
      rw [← (A i).inside_union_boundary]
      exact Or.inr (hbdy.symm ▸ Or.inr hy)
    obtain ⟨N, hNb, _hNs, _hNt, hNp, _hNi, hNA, _hNshort, hNcap, hNrim⟩ :=
      exists_saddle_contained_profile_ball P u (Told i) (hOld i).1
        (hOld i).2.1 (hOld i).2.2.1 (hOld i).2.2.2.1
        (A i) (ell i) W.level (lambda i) tau (hlambda i) hlg hlt hfilled hnorth
    exact ⟨N, hNb, hNp, hNA, hNcap, hNrim⟩
  choose N hNb hNpoint hNcontain hNcap hNrim using hNs
  have hGexists (i : Fin 2) :
      ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        G '' E i = southOld i ∧
        ∀ y ∈ north i ∪ Rold ∪ (A (other i)).closedRegion, G y = y := by
    obtain ⟨ho, ho1, _hlt, _hlg, _hchart, _hsource, _htarget, _hpoint,
      _hinv, hbdy, _hinside, _hregion, _hheight, _hfill, _hcut, hpatch,
      _havoid, hret, hrim⟩ := hA i
    let X := Rold ∪ (A (other i)).closedRegion
    have hX : IsClosed X :=
      hRcompact.isClosed.union (A (other i)).closedRegion_compact.isClosed
    have hp : ∀ q : UnitTwoSphere, -o i < (heightCoordinates (q : E3)).2 →
        (N i).chart (q : E3) ∈ (A i).boundary := by
      intro q hq
      rw [hNpoint]
      exact hpatch q hq
    have hAn : (A i).boundary = E i ∪ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      exact hbdy
    have hNn : (N i).boundary = southOld i ∪ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      exact hNb i
    have hmeet : E i ∩ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} =
        southOld i ∩ (N i).chart ''
          {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      exact hrim.trans (hNrim i).symm
    have hAX : (A i).closedRegion ∩ X ⊆ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      rintro y ⟨hyA, hyR | hyO⟩
      · exact hret ⟨hyA, Or.inl hyR⟩
      · exact False.elim (Set.disjoint_left.mp (hdisother i) hyA hyO)
    obtain ⟨G, _C, hGe, _hGi, hFix, _⟩ :=
      exists_saddle_north_cap_end_transport (A i) (N i) (o i) ho (by linarith) hp
        (hNcontain i) (E i) (southOld i) X hX hAn hNn hmeet hAX
    refine ⟨G, hGe, ?_⟩
    intro y hy
    exact (hFix y (by simpa only [← hNcap i, X, union_assoc] using hy)).1
  choose G hGe hGfix using hGexists
  have hEclosed (i : Fin 2) : E i ⊆ (A i).closedRegion := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hbdy, _⟩ := hA i
    intro y hy
    rw [← (A i).inside_union_boundary, hbdy]
    exact Or.inr (Or.inl hy)
  have hSouthclosed (i : Fin 2) : southOld i ⊆ (A i).closedRegion := by
    intro y hy
    apply hNcontain i
    rw [← (N i).inside_union_boundary, hNb i]
    exact Or.inr (Or.inl hy)
  have hfixedImage (i : Fin 2) (X : Set E3)
      (hX : X ⊆ north i ∪ Rold ∪ (A (other i)).closedRegion) : G i '' X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hGfix i x (hX hx)] using hx
    · intro hy
      exact ⟨y, hy, hGfix i y (hX hy)⟩
  have hGR (i : Fin 2) : G i '' Rold = Rold :=
    hfixedImage i Rold (fun _ hy => Or.inl (Or.inr hy))
  have hG0E1 : G 0 '' E 1 = E 1 := by
    apply hfixedImage 0
    intro y hy
    apply Or.inr
    simpa only [other, Matrix.cons_val_zero] using hEclosed 1 hy
  have hG1south0 : G 1 '' southOld 0 = southOld 0 := by
    apply hfixedImage 1
    intro y hy
    apply Or.inr
    simpa only [other, Matrix.cons_val_one, Matrix.cons_val_zero] using hSouthclosed 0 hy
  let Gold := (G 0).trans (G 1)
  have hG0S : G 0 '' S = Rold ∪ southOld 0 ∪ E 1 := by
    rw [hCover, image_union, image_union, hGR 0, hGe 0, hG0E1]
  have hGold : Gold '' S = Rold ∪ southOld 0 ∪ southOld 1 := by
    calc
      Gold '' S = G 1 '' (G 0 '' S) := by rw [image_image]; rfl
      _ = Rold ∪ southOld 0 ∪ southOld 1 := by
        rw [hG0S, image_union, image_union, hGR 1, hG1south0, hGe 1]
  have hProfile (i : Fin 2) (q : UnitTwoSphere) :
      |lambda i * (P.model q).2| ≤ lambda i * P.heightBound := by
    rw [abs_mul, abs_of_pos (hlambda i)]
    exact mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda i).le
  have hCapPoint (i : Fin 2) (q : UnitTwoSphere) :
      K 1 (Told i ((P.model q).1, W.level + lambda i * (P.model q).2)) =
        P.capMap (T i) z 1 0 (lambda i) q := by
    have hh : |lambda i * (P.model q).2| ≤ e :=
      (hProfile i q).trans ((hlambdab i).trans (by linarith)).le
    have ha := (hAffine (lambda i * (P.model q).2) hh).2
    simp only [SurgeryCapProfile.capMap_apply, one_mul, zero_add, T,
      heightTransportTube_apply, ha]
  have hCaps (i : Fin 2) : K 1 '' southOld i = south i := by
    ext y
    constructor
    · rintro ⟨v, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hCapPoint i q).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Told i ((P.model q).1, W.level + lambda i * (P.model q).2),
        ⟨q, hq, rfl⟩, hCapPoint i q⟩
  have hKR : K 1 '' Rold = R := by
    simpa only [add_zero] using
      (hSets 0 (by simpa only [abs_zero] using he.le)).2.2.2.2.1
  let Gtotal := Gold.trans (K 1)
  have htotal : Gtotal '' S = R ∪ south 0 ∪ south 1 := by
    calc
      Gtotal '' S = K 1 '' (Gold '' S) := by rw [image_image]; rfl
      _ = R ∪ south 0 ∪ south 1 := by
        rw [hGold, image_union, image_union, hKR, hCaps 0, hCaps 1]
  refine ⟨Gtotal, htotal, ?_, ?_, IsCollarEmbedding.postcompose_diffeomorph hpsi Gtotal⟩
  · rw [← htotal]
    exact Gtotal.symm_image_image S
  · intro i y hy
    obtain ⟨q, _hq, rfl⟩ := hy
    have hs : ((P.model q).1, z + lambda i * (P.model q).2) ∈ (T i).source :=
      hSource i ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩
    change |H (P.capMap (T i) z 1 0 (lambda i) q) - z| ≤ lambda i * P.heightBound
    rw [SurgeryCapProfile.capMap_apply, one_mul, zero_add, hTubeHeight i _ hs]
    simpa only [add_sub_cancel_left] using hProfile i q

end PoincareConjecture.M25.Topology3D
