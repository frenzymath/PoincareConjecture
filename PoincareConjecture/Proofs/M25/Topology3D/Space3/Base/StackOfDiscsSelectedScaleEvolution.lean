import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalEvolution

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackCanonicalProfileEvolution_for_scales
    (P : SurgeryCapProfile) (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ t : ℝ, ∀ q : UnitTwoSphere,
        |(stackCapProfilePath P.horizontal a P.vertical b t
          (heightCoordinates (q : E3))).2| ≤ B) ∧
      ∀ (T : OpenPartialHomeomorph (E2 × ℝ) E3),
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source →
        ContDiffOn ℝ ∞ T T.source → ContDiffOn ℝ ∞ T.symm T.target →
        ∀ (u : UnitTwoSphere),
          (∀ p ∈ T.source, inner ℝ (u : E3) (T p) = p.2) →
          ∀ s sigma lambda eta : ℝ, |sigma| = 1 → 0 < lambda → lambda * B < eta →
            ∀ V0 : Set E3, IsOpen V0 →
              T '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ V0 →
              ∃ N : Set E3,
                ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                ∃ K : Set E3,
                  IsOpen N ∧ T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ N ∧
                  N ⊆ T.target ∧
                  ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
                  ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
                  (∀ y, Phi 0 y = y) ∧
                  (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ q ∈ Qminus,
                    Phi t (P.capMap T s sigma 0 lambda q) =
                      stackPlacedProfileCap P.horizontal a P.vertical b T s sigma 0 lambda t q) ∧
                  (∀ q ∈ Qminus,
                    Phi 1 (P.capMap T s sigma 0 lambda q) =
                      T ((M (heightCoordinates (q : E3))).1,
                        s + sigma * lambda * (M (heightCoordinates (q : E3))).2)) ∧
                  (let Y := (fun q : UnitTwoSphere =>
                    T ((M (heightCoordinates (q : E3))).1,
                      s + sigma * lambda * (M (heightCoordinates (q : E3))).2)) '' Qminus
                   Phi 1 '' (P.capMap T s sigma 0 lambda '' Qminus) = Y ∧
                     (Phi 1).symm '' Y = P.capMap T s sigma 0 lambda '' Qminus) ∧
                  IsCompact K ∧
                  K ⊆ (((V0 ∩ T.target) ∩
                    {y | |inner ℝ (u : E3) y - s| < eta}) ∩
                    {y | sigma * (inner ℝ (u : E3) y - s) < 0}) \ N ∧
                  (∀ t, tsupport (fun y => Phi t y - y) ⊆ K ∧
                    tsupport (fun y => (Phi t).symm y - y) ⊆ K) ∧
                  (∀ t y, y ∉ K → Phi t y = y ∧ (Phi t).symm y = y) ∧
                  (∀ t y, y ∈ N → Phi t y = y ∧ (Phi t).symm y = y) ∧
                  ∀ t y, 0 ≤ sigma * (inner ℝ (u : E3) y - s) →
                    Phi t y = y ∧ (Phi t).symm y = y := by
  dsimp only
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  obtain ⟨ha, hapos, _, habound, _, _, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨hb, hbpos, _, _, _, _⟩ :=
    stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  obtain ⟨B, hB, hbound⟩ := exists_stackCapProfilePath_height_bound
    P.horizontal a P.vertical b P.horizontal_smooth ha P.vertical_smooth hb
  refine ⟨B, hB, hbound, ?_⟩
  intro T hsource hT hTi u hheight s sigma lambda eta hsign hlambda hsmall V0 hV0 hstack
  let cap := stackPlacedProfileCap P.horizontal a P.vertical b T s sigma 0 lambda
  let V := V0 ∩ {y | |inner ℝ (u : E3) y - s| < eta}
  have hV : IsOpen V := hV0.inter (isOpen_lt
    (((innerSL ℝ (u : E3)).continuous.sub continuous_const).abs) continuous_const)
  have htrackV (t : ℝ) (q : UnitTwoSphere) : cap t q ∈ V := by
    let p := stackCapProfilePath P.horizontal a P.vertical b t (heightCoordinates (q : E3))
    have hrad : p.1 ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr
      (stackCapProfilePath_fst_norm_le P.horizontal a P.vertical b
        P.horizontal_smooth ha P.vertical_smooth hb P.horizontal_pos hapos
        P.vertical_pos hbpos P.horizontal_bound habound t
        (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q).le)
    have habs : |sigma * (lambda * p.2)| < eta := by
      rw [abs_mul, abs_mul, hsign, abs_of_pos hlambda, one_mul]
      exact (mul_le_mul_of_nonneg_left (hbound t q) hlambda.le).trans_lt hsmall
    have hinterval : s + sigma * (0 + lambda * p.2) ∈ Icc (s - eta) (s + eta) := by
      simp only [zero_add]
      constructor <;> linarith [(abs_lt.mp habs).1, (abs_lt.mp habs).2]
    have hsrc : (p.1, s + sigma * (0 + lambda * p.2)) ∈ T.source :=
      hsource ⟨hrad, mem_univ _⟩
    refine ⟨hstack ⟨(p.1, s + sigma * (0 + lambda * p.2)), ⟨hrad, hinterval⟩, rfl⟩, ?_⟩
    change |inner ℝ (u : E3) (T (p.1, s + sigma * (0 + lambda * p.2))) - s| < eta
    rw [hheight _ hsrc]
    simpa only [zero_add, add_sub_cancel_left] using habs
  obtain ⟨hdelta, hW, hcircle, ha0near, ha1near, hb0near, hb1near, _⟩ :=
    exists_stackCanonicalProfile_common_germ P rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1
  obtain ⟨N, Phi, K, hN, hseam, hNt, hPhi, hPhii, hzero, htrack, _himage,
      hK, hKs, hs, his, hfix, hfixN, hfixIn⟩ :=
    exists_stackPlacedProfileEvolution P.horizontal a P.vertical b
      P.horizontal_smooth ha P.vertical_smooth hb P.horizontal_pos hapos
      P.vertical_pos hbpos P.horizontal_bound habound T hsource hT hTi u hheight
      s sigma 0 lambda hsign hlambda (min v0 (1 / 4)) hdelta
      {x : E2 | max rOne (1 / 2) < ‖x‖} hW hcircle
      ha0near ha1near hb0near hb1near hV (fun t _ q _ => htrackV t q)
  have hMone (p : E2 × ℝ) : stackCapProfilePath P.horizontal a P.vertical b 1 p = M p := by
    simp only [M, stackCapProfilePath,
      stackProfileBlend_of_one_le P.horizontal a 1 le_rfl,
      stackProfileBlend_of_one_le P.vertical b 1 le_rfl,
      stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  have hcapzero (q : UnitTwoSphere) : cap 0 q = P.capMap T s sigma 0 lambda q :=
    (stackPlacedProfileCap_endpoints P.horizontal a P.vertical b
      P.horizontal_smooth ha P.vertical_smooth hb P.horizontal_pos hapos
      P.vertical_pos hbpos T s sigma 0 lambda q).1
  have hcapone (q : UnitTwoSphere) : cap 1 q =
      T ((M (heightCoordinates (q : E3))).1,
        s + sigma * lambda * (M (heightCoordinates (q : E3))).2) := by
    change T _ = T _
    simp only [hMone, zero_add, mul_assoc]
  have htrack' (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) (q : UnitTwoSphere)
      (hq : q ∈ Qminus) : Phi t (P.capMap T s sigma 0 lambda q) = cap t q := by
    rw [← hcapzero]
    exact htrack t ht q hq
  have hend (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      Phi 1 (P.capMap T s sigma 0 lambda q) =
        T ((M (heightCoordinates (q : E3))).1,
          s + sigma * lambda * (M (heightCoordinates (q : E3))).2) :=
    (htrack' 1 (by norm_num) q hq).trans (hcapone q)
  refine ⟨N, Phi, K, hN, ?_, hNt, hPhi, hPhii, hzero, htrack', hend, ?_, hK,
    ?_, (fun t => ⟨hs t, his t⟩), hfix, hfixN, ?_⟩
  · simpa only [mul_zero, add_zero] using hseam
  · constructor
    · rw [image_image]
      exact image_congr hend
    · apply Subset.antisymm
      · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨q, hq, (Diffeomorph.symm_apply_apply (Phi 1) _).symm.trans
          (congrArg (Phi 1).symm (hend q hq))⟩
      · rintro _ ⟨q, hq, rfl⟩
        refine ⟨Phi 1 (P.capMap T s sigma 0 lambda q), ⟨q, hq, (hend q hq).symm⟩, ?_⟩
        exact Diffeomorph.symm_apply_apply _ _
  · intro y hy
    have hm := hKs hy
    refine ⟨⟨⟨⟨hm.1.1.1.1, hm.1.1.2⟩, hm.1.1.1.2⟩, ?_⟩, hm.2⟩
    simpa only [mul_zero, add_zero] using hm.1.2
  · intro t y hy
    apply hfixIn t y
    simpa only [mul_zero, add_zero] using hy

end PoincareConjecture.M25.Topology3D
