import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.NestedPairFilledSidesCore

namespace PoincareConjecture.M25.Topology3D

open Set Metric Function
open scoped ContDiff Manifold Topology

set_option linter.unusedVariables false in
set_option maxHeartbeats 3000000 in




theorem exists_saddle_nested_pair_filled_sides
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmuSmall : mu ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let other : Fin 2 → Fin 2 := Equiv.swap (0 : Fin 2) 1
    let K : Set E2 := kappa '' closedBall (0 : E2) 1
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i *
        Real.sqrt ((J2 x).1 ^ 2 + mu)}
    let Short : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧ Real.sqrt ((J2 x).1 ^ 2 + mu) < sign i * (J2 x).2}
    let Long : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧ sign i * (J2 x).2 <
        Real.sqrt ((J2 x).1 ^ 2 + mu)}
    let Eta : Fin 2 → Set E2 := fun i =>
      kappa '' ((F 1) '' Z i)
    ∀ (nu : ℝ) (hnu : 0 < nu) (hnuSmall : nu < 1 / 16)
      (alpha : Fin 2 → Fin 2 → ℝ → E2)
      (hAlpha : ∀ j i,
        ContDiffOn ℝ ∞ (alpha j i) (Ioo (-nu) (1 + nu)))
      (hProper : ∀ j i, alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ)
      (hInitial : ∀ j i t, |t| < nu →
        alpha j i t = kappa ((1 + t) • port (ep (i, 0))))
      (hTerminal : ∀ j i t, |t - 1| < nu →
        alpha j i t = kappa ((2 - t) • port (ep (i, 1))))
      (B : Fin 2 → Fin 2 → BallNeighborhoodChart E2 E2)
      (hBoundary : ∀ j i,
        (B j i).boundary = (alpha j i '' Icc (0 : ℝ) 1) ∪ Eta i)
      (inner : Fin 2)
      (hNested : ∀ j, (B j inner).closedRegion ⊆
        (B j (other inner)).inside),
      ∃ h : ℝ,
        0 < h ∧ h < nu / 128 ∧ h < 1 / 1024 ∧
        (∀ j,
          kappa '' ((F 1) '' Short inner) ⊆ (B j inner).inside ∧
          kappa '' ((F 1) '' Long inner) ⊆ (B j inner).closedRegionᶜ ∧
          kappa '' ((F 1) '' Long (other inner)) ⊆
            (B j (other inner)).inside ∧
          kappa '' ((F 1) '' Short (other inner)) ⊆
            (B j (other inner)).closedRegionᶜ) ∧
        (∀ j i,
          (alpha j i '' Icc (0 : ℝ) 1) ∩
              (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
            kappa '' (((fun r : ℝ => r • port (ep (i, 0))) ''
                Icc 1 (1 + 32 * h)) ∪
              ((fun r : ℝ => r • port (ep (i, 1))) ''
                Icc 1 (1 + 32 * h)))) ∧
        (∀ j,
          kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
              |(J2 x).1| < sign inner * (J2 x).2} ⊆
            (B j inner).inside) ∧
        ∀ j,
          kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h ∧
              |(J2 x).1| ≤ sign inner * (J2 x).2} ⊆
            (B j inner).closedRegion := by
  classical
  dsimp only
  intro nu _hnu _hnuSmall alpha _hAlpha _hProper _hInitial _hTerminal B
    _hBoundary inner _hNested
  let muFam : Fin 2 → ℝ := fun _ => mu
  have hmuFam : ∀ j, 0 < muFam j := fun _ => hmu
  have hmuSmallFam : ∀ j, muFam j ≤ 1 / 128 := fun _ => hmuSmall
  have hfamily := exists_saddle_nested_pair_filled_sides_family
    kappa hkappaSource J2 hJ2 muFam hmuFam hmuSmallFam chi hchi
      hchiBounds hchiSupport hchiOne nu _hnu _hnuSmall alpha _hAlpha _hProper
      _hInitial _hTerminal B _hBoundary inner _hNested
  simpa only [muFam] using hfamily

end PoincareConjecture.M25.Topology3D
