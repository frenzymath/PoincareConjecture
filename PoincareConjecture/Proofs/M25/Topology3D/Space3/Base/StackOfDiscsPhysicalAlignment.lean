import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalAlignment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsClampedTransition












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackPhysicalCanonicalCapAlignment
    (U V : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ContDiffOn ℝ ∞ U U.source) (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (u : UnitTwoSphere)
    (hUh : ∀ p ∈ U.source, inner ℝ (u : E3) (U p) = p.2)
    (hVh : ∀ p ∈ V.source, inner ℝ (u : E3) (V p) = p.2)
    (I : Set ℝ) (hI : IsCompact I)
    (hUs : closedBall (0 : E2) 1 ×ˢ I ⊆ U.source)
    (hVs : closedBall (0 : E2) 1 ×ˢ I ⊆ V.source)
    (hboundary : ∀ z ∈ I,
      (fun x : E2 => U (x, z)) '' sphere (0 : E2) 1 =
        (fun x : E2 => V (x, z)) '' sphere (0 : E2) 1)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (hkI : ∀ z, k z ∈ I)
    (L A a b B R : ℝ)
    (hLA : L < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hBR : B < R)
    (hkfix : ∀ z ∈ Icc A B, k z = z)
    (O : Set E3) (hO : IsOpen O)
    (hcircleO : V '' (sphere (0 : E2) 1 ×ˢ Icc A B) ⊆ O) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 4 ∧
      ∃ Psi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ K : Set E3,
        IsCompact K ∧ K ⊆ O ∧ K ⊆ {y | inner ℝ (u : E3) y ∈ Ioo A B} ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => Psi p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => (Psi p.1).symm p.2) ∧
        (∀ y, Psi 0 y = y) ∧
        (∀ t, tsupport (fun y => Psi t y - y) ⊆ K ∧
          tsupport (fun y => (Psi t).symm y - y) ⊆ K) ∧
        (∀ t y, y ∉ K → Psi t y = y ∧ (Psi t).symm y = y) ∧
        (∀ t y, inner ℝ (u : E3) (Psi t y) = inner ℝ (u : E3) y ∧
          inner ℝ (u : E3) ((Psi t).symm y) = inner ℝ (u : E3) y) ∧
        (∀ t z, z ∈ Icc A B → ∀ q ∈ sphere (0 : E2) 1,
          Psi t (V (q, z)) = V (q, z) ∧ (Psi t).symm (V (q, z)) = V (q, z)) ∧
        ∀ s sigma lambda gamma rFlat rOne v0 v1 : ℝ,
          |sigma| = 1 → 0 < lambda → lambda < gamma →
          a ≤ s - gamma → s + gamma ≤ b →
          0 < rFlat → 1 - delta < rFlat → rFlat < rOne → rOne < 1 →
          0 < v0 → v0 < v1 → v1 < 1 → v1 ^ 2 + rOne ^ 2 < 1 →
          let ah := stackCanonicalHorizontal v0 v1
          let bv := stackCanonicalVertical rFlat rOne
          let M := stackCapProfilePath ah ah bv bv 0
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let Y := (fun q : UnitTwoSphere =>
            ((M (heightCoordinates (q : E3))).1,
              s + sigma * lambda * (M (heightCoordinates (q : E3))).2)) '' Qminus
          Y ⊆ U.source ∧ Y ⊆ V.source ∧
            Psi 1 '' (U '' Y) = V '' Y ∧ (Psi 1).symm '' (V '' Y) = U '' Y := by
  let L0 := heightPlaneCoordinates u
  let SW := ContinuousLinearEquiv.prodComm ℝ ℝ E2
  let H := L0.trans SW.symm
  let U0 := U.transHomeomorph L0.toHomeomorph
  let V0 := V.transHomeomorph L0.toHomeomorph
  have hU0 : ContDiffOn ℝ ∞ U0 U0.source := L0.contDiff.comp_contDiffOn hU
  have hV0 : ContDiffOn ℝ ∞ V0 V0.source := L0.contDiff.comp_contDiffOn hV
  have hU0i : ContDiffOn ℝ ∞ U0.symm U0.target :=
    hUi.comp L0.symm.contDiff.contDiffOn (fun _ hp => hp)
  have hV0i : ContDiffOn ℝ ∞ V0.symm V0.target :=
    hVi.comp L0.symm.contDiff.contDiffOn (fun _ hp => hp)
  have hU0h (p : E2 × ℝ) (hp : p ∈ U0.source) : (U0 p).2 = p.2 :=
    (heightPlaneCoordinates_snd u (U p)).trans (hUh p hp)
  have hV0h (p : E2 × ℝ) (hp : p ∈ V0.source) : (V0 p).2 = p.2 :=
    (heightPlaneCoordinates_snd u (V p)).trans (hVh p hp)
  have hcircles (z : ℝ) (hz : z ∈ I) :
      (fun x : E2 => (V0 (x, z)).1) '' sphere (0 : E2) 1 =
        (fun x : E2 => (U0 (x, z)).1) '' sphere (0 : E2) 1 := by
    calc
      (fun x : E2 => (V0 (x, z)).1) '' sphere (0 : E2) 1 =
          (fun y : E3 => (L0 y).1) '' ((fun x : E2 => V (x, z)) '' sphere 0 1) :=
        (image_image (fun y : E3 => (L0 y).1) (fun x : E2 => V (x, z))
          (sphere (0 : E2) 1)).symm
      _ = (fun y : E3 => (L0 y).1) '' ((fun x : E2 => U (x, z)) '' sphere 0 1) :=
        congrArg (image (fun y : E3 => (L0 y).1)) (hboundary z hz).symm
      _ = (fun x : E2 => (U0 (x, z)).1) '' sphere (0 : E2) 1 :=
        image_image (fun y : E3 => (L0 y).1) (fun x : E2 => U (x, z))
          (sphere (0 : E2) 1)
  obtain ⟨r, hr, E, _hEf, _hEif, _hEsEq, _hEtEq, hE, hEi, hEh,
      hEs, hEt, hEproduct, hfixed⟩ :=
    exists_stackClampedDiscTransition V0 U0 hV0 hV0i hU0 hU0i hV0h hU0h
      I hI hVs hUs hcircles k hk hkI
  let U1 := (SW.toHomeomorph.transOpenPartialHomeomorph U0).transHomeomorph
    SW.symm.toHomeomorph
  let V1 := (SW.toHomeomorph.transOpenPartialHomeomorph V0).transHomeomorph
    SW.symm.toHomeomorph
  have hU1f (p : ℝ × E2) : U1 p = H (U (p.2, p.1)) := rfl
  have hV1f (p : ℝ × E2) : V1 p = H (V (p.2, p.1)) := rfl
  have hU1 : ContDiffOn ℝ ∞ U1 U1.source :=
    SW.symm.contDiff.comp_contDiffOn
      (hU0.comp SW.contDiff.contDiffOn (fun _ hp => hp))
  have hV1 : ContDiffOn ℝ ∞ V1 V1.source :=
    SW.symm.contDiff.comp_contDiffOn
      (hV0.comp SW.contDiff.contDiffOn (fun _ hp => hp))
  have hU1i : ContDiffOn ℝ ∞ U1.symm U1.target :=
    SW.symm.contDiff.comp_contDiffOn
      (hU0i.comp SW.contDiff.contDiffOn (fun _ hp => hp))
  have hV1i : ContDiffOn ℝ ∞ V1.symm V1.target :=
    SW.symm.contDiff.comp_contDiffOn
      (hV0i.comp SW.contDiff.contDiffOn (fun _ hp => hp))
  have hU1h (p : ℝ × E2) (hp : p ∈ U1.source) : (U1 p).1 = p.1 :=
    hU0h (SW p) hp
  have hV1h (p : ℝ × E2) (hp : p ∈ V1.source) : (V1 p).1 = p.1 :=
    hV0h (SW p) hp
  have hband (z : ℝ) (hz : z ∈ Icc A B) : z ∈ I := hkfix z hz ▸ hkI z
  have hU1s : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ U1.source :=
    fun p hp => hUs ⟨hp.2, hband p.1 hp.1⟩
  have hV1s : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ V1.source :=
    fun p hp => hVs ⟨hp.2, hband p.1 hp.1⟩
  have htransition (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) : U1 (E (z, q)) = V1 (z, q) := by
    have hh := (hfixed z (hkfix z hz) q (sphere_subset_closedBall hq)).2.1
    change SW.symm (U0 ((E (z, q)).2, (E (z, q)).1)) = SW.symm (V0 (q, z))
    rw [(hEh (z, q)).1]
    exact congrArg SW.symm hh
  let O1 := H.symm ⁻¹' O
  have hO1 : IsOpen O1 := hO.preimage H.symm.continuous
  have hcircleO1 : V1 '' (Icc A B ×ˢ sphere (0 : E2) 1) ⊆ O1 := by
    rintro _ ⟨p, hp, rfl⟩
    change H.symm (V1 p) ∈ O
    rw [hV1f, H.symm_apply_apply]
    exact hcircleO ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, rfl⟩
  obtain ⟨delta, hd, hdq, F, S, hS, hSO, hSband, hF, hFi, hF0,
      _hSupport, hFix, hHeight, hCircle, hCaps⟩ :=
    exists_stackCanonicalCapAlignment E U1 V1 hE hEi hU1 hU1i hV1 hV1i
      (fun p _ => (hEh p).1) hU1h hV1h
      (fun _ hp => hEs ⟨hp.1, closedBall_subset_ball hr hp.2⟩)
      (fun _ hp => hEt ⟨hp.1, closedBall_subset_ball hr hp.2⟩)
      hEproduct L A a b B R hLA hAa hab hbB hBR hU1s hV1s htransition
      O1 hO1 hcircleO1
  let Psi := fun t : ℝ => (H.toDiffeomorph.trans (F t)).trans H.symm.toDiffeomorph
  let K := H.symm '' S
  have hK : IsCompact K := hS.image H.symm.continuous
  have hKO : K ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact hSO hp
  have hHheight (y : E3) : (H y).1 = inner ℝ (u : E3) y :=
    heightPlaneCoordinates_snd u y
  have hKband : K ⊆ {y | inner ℝ (u : E3) y ∈ Ioo A B} := by
    rintro _ ⟨p, hp, rfl⟩
    change inner ℝ (u : E3) (H.symm p) ∈ Ioo A B
    rw [← hHheight, H.apply_symm_apply]
    exact (hSband hp).1
  have hPsi : ContDiff ℝ ∞ (fun p : ℝ × E3 => Psi p.1 p.2) :=
    H.symm.contDiff.comp (hF.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  have hPsii : ContDiff ℝ ∞ (fun p : ℝ × E3 => (Psi p.1).symm p.2) :=
    H.symm.contDiff.comp (hFi.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  have hboth (t : ℝ) (y : E3) (hy : y ∉ K) :
      Psi t y = y ∧ (Psi t).symm y = y := by
    have hout : H y ∉ S := fun hp => hy ⟨H y, hp, H.symm_apply_apply y⟩
    change H.symm (F t (H y)) = y ∧ H.symm ((F t).symm (H y)) = y
    rw [(hFix t (H y) hout).1, (hFix t (H y) hout).2, H.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  refine ⟨delta, hd, hdq, Psi, K, hK, hKO, hKband, hPsi, hPsii,
    ?_, ?_, hboth, ?_, ?_, ?_⟩
  · intro y
    change H.symm (F 0 (H y)) = y
    rw [hF0, H.symm_apply_apply]
  · intro t
    constructor
    · apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      exact hy (sub_eq_zero.mpr (hboth t y hyK).1)
    · apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      exact hy (sub_eq_zero.mpr (hboth t y hyK).2)
  · intro t y
    have hf : H (Psi t y) = F t (H y) := H.apply_symm_apply _
    have hi : H ((Psi t).symm y) = (F t).symm (H y) := H.apply_symm_apply _
    constructor
    · simpa only [hHheight] using
        (congrArg Prod.fst hf).trans (hHeight t (H y)).1
    · simpa only [hHheight] using
        (congrArg Prod.fst hi).trans (hHeight t (H y)).2
  · intro t z hz q hq
    have hh := hCircle t z hz q hq
    rw [hV1f] at hh
    change H.symm (F t (H (V (q, z)))) = V (q, z) ∧
      H.symm ((F t).symm (H (V (q, z)))) = V (q, z)
    rw [hh.1, hh.2, H.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  · intro s sigma lambda gamma rFlat rOne v0 v1 hsigma hlambda hlg hleft hright
      hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
    obtain ⟨hYU1, hYV1, hf, _hi⟩ := hCaps s sigma lambda gamma rFlat rOne v0 v1
      hsigma hlambda hlg hleft hright hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
    let ah := stackCanonicalHorizontal v0 v1
    let bv := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath ah ah bv bv 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let Y := (fun q : UnitTwoSphere =>
      ((M (heightCoordinates (q : E3))).1,
        s + sigma * lambda * (M (heightCoordinates (q : E3))).2)) '' Qminus
    let Y1 := (fun q : UnitTwoSphere =>
      (s + sigma * lambda * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus
    change Y1 ⊆ U1.source at hYU1
    change Y1 ⊆ V1.source at hYV1
    change F 1 '' (U1 '' Y1) = V1 '' Y1 at hf
    have hUimage : H '' (U '' Y) = U1 '' Y1 := by
      dsimp only [Y, Y1]
      rw [image_image U, image_image H, image_image U1]
      rfl
    have hVimage : H '' (V '' Y) = V1 '' Y1 := by
      dsimp only [Y, Y1]
      rw [image_image V, image_image H, image_image V1]
      rfl
    have hforward : Psi 1 '' (U '' Y) = V '' Y := by
      calc
        Psi 1 '' (U '' Y) = H.symm '' (F 1 '' (H '' (U '' Y))) := by
          simp only [Psi, Diffeomorph.coe_trans, image_comp]
          rfl
        _ = H.symm '' (V1 '' Y1) := by rw [hUimage, hf]
        _ = H.symm '' (H '' (V '' Y)) := congrArg (image H.symm) hVimage.symm
        _ = V '' Y := by
          rw [image_image]
          simp only [H.symm_apply_apply, image_id']
    refine ⟨?_, ?_, hforward, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hYU1 ⟨q, hq, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hYV1 ⟨q, hq, rfl⟩
    · change (Psi 1).symm '' (V '' Y) = U '' Y
      rw [← hforward, image_image]
      simp only [Diffeomorph.symm_apply_apply, image_id']

end PoincareConjecture.M25.Topology3D
