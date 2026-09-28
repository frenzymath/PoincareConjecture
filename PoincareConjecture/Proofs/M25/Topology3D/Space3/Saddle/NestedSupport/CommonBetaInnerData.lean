import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaPackets

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

noncomputable section

def saddleNestedInnerSx : Fin 4 → ℝ := ![1, -1, -1, 1]

def saddleNestedInnerSy : Fin 4 → ℝ := ![1, 1, -1, -1]

def saddleNestedInnerEp : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

def saddleNestedInnerPort (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (i e : Fin 2) : E2 :=
  J2.symm (saddleNestedInnerSx (saddleNestedInnerEp (i, e)) / Real.sqrt 2,
    saddleNestedInnerSy (saddleNestedInnerEp (i, e)) / Real.sqrt 2)

structure CommonBetaInnerShortData
    (kappa : OpenPartialHomeomorph E2 E2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (h : ℝ) (inner : Fin 2) where
  beta : ℝ → E2
  b : ℝ → E2
  gamma : ℝ → E2
  g : ℝ → E2
  w : ℝ
  hw : 0 < w
  N : OpenPartialHomeomorph (ℝ × ℝ) E2
  hBetaDef : beta = kappa ∘ b
  hGammaDef : gamma = kappa ∘ g
  hBetaData : ContDiffOn ℝ ∞ beta (Ioo (-h / 8) (1 + h / 8)) ∧
    InjOn beta (Ioo (-h / 8) (1 + h / 8)) ∧
    ∀ t ∈ Ioo (-h / 8) (1 + h / 8), deriv beta t ≠ 0
  hGammaData : ContDiffOn ℝ ∞ gamma (Ioo (-h / 8) (1 + h / 8)) ∧
    InjOn gamma (Ioo (-h / 8) (1 + h / 8)) ∧
    ∀ t ∈ Ioo (-h / 8) (1 + h / 8), deriv gamma t ≠ 0
  hGerms : ∀ t ∈ Ioo (-h / 8) (1 + h / 8),
    (t ≤ 4 * h → beta t = kappa ((1 + t) • saddleNestedInnerPort J2 inner 0)) ∧
    (1 - 4 * h ≤ t → beta t = kappa ((2 - t) • saddleNestedInnerPort J2 inner 1)) ∧
    (t ≤ h → gamma t = kappa ((1 + 3 * h - t) • saddleNestedInnerPort J2 inner 1)) ∧
    (1 - h ≤ t → gamma t = kappa ((1 + 3 * h + t - 1) • saddleNestedInnerPort J2 inner 0))
  hBetaRange : MapsTo b (Icc (0 : ℝ) 1)
    {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 6 * h ∧
      |(J2 x).1| ≤ (![1, -1] inner) * (J2 x).2}
  hGammaRange : MapsTo g (Icc (0 : ℝ) 1)
    {x : E2 | 1 + h ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 3 * h ∧
      |(J2 x).1| ≤ (![1, -1] inner) * (J2 x).2}
  hBetaProper : beta '' Ioo (0 : ℝ) 1 ⊆
    (kappa '' closedBall (0 : E2) 1)ᶜ
  hGammaProper : gamma '' Ioo (-h / 8) (1 + h / 8) ⊆
    (kappa '' closedBall (0 : E2) 1)ᶜ
  hBetaCut : ∀ t ∈ Icc (3 * h) (1 - 3 * h),
    1 + 3 * h ≤ ‖b t‖ ∧
      (‖b t‖ = 1 + 3 * h ↔ t = 3 * h ∨ t = 1 - 3 * h)
  hGammaCut : ∀ t ∈ Icc (0 : ℝ) 1,
    ‖g t‖ = 1 + 3 * h ↔ t = 0 ∨ t = 1
  hJoins : gamma 0 = beta (1 - 3 * h) ∧
    gamma 1 = beta (3 * h) ∧
    (gamma '' Icc (0 : ℝ) 1) ∩ (beta '' Icc (3 * h) (1 - 3 * h)) =
      {beta (3 * h), beta (1 - 3 * h)} ∧
    gamma (1 / 2) = kappa (J2.symm (0, (![1, -1] inner) * (1 + h)))
  hNsource : Icc (-h / 16) (1 + h / 16) ×ˢ Icc (-w) w ⊆ N.source
  hNsubset : N.source ⊆ Ioo (-h / 8) (1 + h / 8) ×ˢ (univ : Set ℝ)
  hNtarget : N.target ⊆ kappa.target
  hN : ContDiffOn ℝ ∞ N N.source
  hNi : ContDiffOn ℝ ∞ N.symm N.target
  hNform : ∀ p ∈ N.source,
    N p = gamma p.1 + p.2 •
      (J2.symm (-(J2 (deriv gamma p.1)).2, (J2 (deriv gamma p.1)).1))

structure CommonBetaInnerFilledData
    (kappa : OpenPartialHomeomorph E2 E2)
    (Bi : Fin 2 → BallNeighborhoodChart E2 E2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (h : ℝ) (inner : Fin 2) where
  filled : Fin 2 → E2 → E2
  longSide : Fin 2 → Set E2
  hLong : ∀ j, kappa '' (filled j '' longSide j) ⊆
    (Bi j).closedRegionᶜ
  hZero : ∀ j, (0 : E2) ∈ filled j '' longSide j

end

end PoincareConjecture.M25.Topology3D
