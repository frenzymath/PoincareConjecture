import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsSelectedScaleEvolution

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackOriginalProfileAlignment
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
      ∀ (U V : OpenPartialHomeomorph (E2 × ℝ) E3),
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ U.source →
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ V.source →
        ContDiffOn ℝ ∞ U U.source → ContDiffOn ℝ ∞ U.symm U.target →
        ContDiffOn ℝ ∞ V V.source → ContDiffOn ℝ ∞ V.symm V.target →
        ∀ (u : UnitTwoSphere),
          (∀ p ∈ U.source, inner ℝ (u : E3) (U p) = p.2) →
          (∀ p ∈ V.source, inner ℝ (u : E3) (V p) = p.2) →
          ∀ s sigma lambda eta : ℝ, |sigma| = 1 → 0 < lambda → lambda * B < eta →
            ∀ OU OV : Set E3, IsOpen OU → IsOpen OV →
              U '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ OU →
              V '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ OV →
              ∀ A : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                (let Y := (fun q : UnitTwoSphere =>
                  ((M (heightCoordinates (q : E3))).1,
                    s + sigma * lambda * (M (heightCoordinates (q : E3))).2)) '' Qminus
                 A '' (U '' Y) = V '' Y) →
                ∀ S : Set E3, IsCompact S →
                  (∀ y, y ∉ S → A y = y ∧ A.symm y = y) →
                  ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                    ∃ K : Set E3,
                      F '' (P.capMap U s sigma 0 lambda '' Qminus) =
                        P.capMap V s sigma 0 lambda '' Qminus ∧
                      F.symm '' (P.capMap V s sigma 0 lambda '' Qminus) =
                        P.capMap U s sigma 0 lambda '' Qminus ∧
                      IsCompact K ∧ K ⊆ OU ∪ S ∪ OV ∧
                      tsupport (fun y => F y - y) ⊆ K ∧
                      tsupport (fun y => F.symm y - y) ⊆ K ∧
                      (∀ y, y ∉ K → F y = y ∧ F.symm y = y) ∧
                      ∀ y, A y = y →
                        (0 ≤ sigma * (inner ℝ (u : E3) y - s) ∨
                          (y ∉ OU ∧ y ∉ OV)) →
                        F y = y ∧ F.symm y = y := by
  dsimp only
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  obtain ⟨B, hB, hbound, hflows⟩ := exists_stackCanonicalProfileEvolution_for_scales
    P rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1
  refine ⟨B, hB, hbound, ?_⟩
  intro U V hUs hVs hU hUi hV hVi u hUh hVh s sigma lambda eta hsign hlambda hsmall
    OU OV hOU hOV hUstack hVstack A hA S hS hAfix
  obtain ⟨_NU, PhiU, KU, _hNU, _hUseam, _hNUt, _hPhiU, _hPhiUi, _hUzero,
      _hUtrack, _hUend, hUimages, hKU, hKUs, _hUsupport, hUfix, _hUfixN, hUin⟩ :=
    hflows U hUs hU hUi u hUh s sigma lambda eta hsign hlambda hsmall OU hOU hUstack
  obtain ⟨_NV, PhiV, KV, _hNV, _hVseam, _hNVt, _hPhiV, _hPhiVi, _hVzero,
      _hVtrack, _hVend, hVimages, hKV, hKVs, _hVsupport, hVfix, _hVfixN, hVin⟩ :=
    hflows V hVs hV hVi u hVh s sigma lambda eta hsign hlambda hsmall OV hOV hVstack
  let Y := (fun q : UnitTwoSphere =>
    ((M (heightCoordinates (q : E3))).1,
      s + sigma * lambda * (M (heightCoordinates (q : E3))).2)) '' Qminus
  change A '' (U '' Y) = V '' Y at hA
  have hUimage : PhiU 1 '' (P.capMap U s sigma 0 lambda '' Qminus) = U '' Y := by
    rw [image_image U]
    exact hUimages.1
  have hVimage : (PhiV 1).symm '' (V '' Y) = P.capMap V s sigma 0 lambda '' Qminus := by
    rw [image_image V]
    exact hVimages.2
  let F := ((PhiU 1).trans A).trans (PhiV 1).symm
  let K := KU ∪ S ∪ KV
  have hK : IsCompact K := (hKU.union hS).union hKV
  have hKUO : KU ⊆ OU := fun _ hy => (hKUs hy).1.1.1.1
  have hKVO : KV ⊆ OV := fun _ hy => (hKVs hy).1.1.1.1
  have hKsub : K ⊆ OU ∪ S ∪ OV := union_subset_union
    (union_subset_union hKUO subset_rfl) hKVO
  have hFimage : F '' (P.capMap U s sigma 0 lambda '' Qminus) =
      P.capMap V s sigma 0 lambda '' Qminus := by
    calc
      F '' (P.capMap U s sigma 0 lambda '' Qminus) =
          (PhiV 1).symm '' (A '' (PhiU 1 '' (P.capMap U s sigma 0 lambda '' Qminus))) := by
        simp only [F, Diffeomorph.coe_trans, image_comp]
      _ = (PhiV 1).symm '' (V '' Y) := by rw [hUimage, hA]
      _ = P.capMap V s sigma 0 lambda '' Qminus := hVimage
  have hFiimage : F.symm '' (P.capMap V s sigma 0 lambda '' Qminus) =
      P.capMap U s sigma 0 lambda '' Qminus := by
    rw [← hFimage, image_image]
    simp only [F.symm_apply_apply, image_id']
  have hFfix (y : E3) (hy : y ∉ K) : F y = y ∧ F.symm y = y := by
    have hu := hUfix 1 y (fun h => hy (Or.inl (Or.inl h)))
    have ha := hAfix y (fun h => hy (Or.inl (Or.inr h)))
    have hv := hVfix 1 y (fun h => hy (Or.inr h))
    change (PhiV 1).symm (A (PhiU 1 y)) = y ∧ (PhiU 1).symm (A.symm (PhiV 1 y)) = y
    rw [hu.1, ha.1, hv.2, hv.1, ha.2, hu.2]
    exact ⟨rfl, rfl⟩
  refine ⟨F, K, hFimage, hFiimage, hK, hKsub, ?_, ?_, hFfix, ?_⟩
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hFfix y hyK).1)
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hFfix y hyK).2)
  · intro y hAy hprotected
    have hAi : A.symm y = y :=
      (congrArg A.symm hAy).symm.trans (A.symm_apply_apply y)
    have hu : PhiU 1 y = y ∧ (PhiU 1).symm y = y := by
      rcases hprotected with hin | hout
      · exact hUin 1 y hin
      · exact hUfix 1 y (fun h => hout.1 (hKUO h))
    have hv : PhiV 1 y = y ∧ (PhiV 1).symm y = y := by
      rcases hprotected with hin | hout
      · exact hVin 1 y hin
      · exact hVfix 1 y (fun h => hout.2 (hKVO h))
    change (PhiV 1).symm (A (PhiU 1 y)) = y ∧ (PhiU 1).symm (A.symm (PhiV 1 y)) = y
    rw [hu.1, hAy, hv.2, hv.1, hAi, hu.2]
    exact ⟨rfl, rfl⟩

end PoincareConjecture.M25.Topology3D
