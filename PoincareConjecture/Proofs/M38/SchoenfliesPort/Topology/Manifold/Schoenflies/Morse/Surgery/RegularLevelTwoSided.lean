import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Preparation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.TwoSided







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)





theorem exists_regular_level_two_sided_surgery_of_smooth
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hne : (h ⁻¹' {c}).Nonempty) {R : Real} (hR : 0 < R) :
    ∃ p : S2, h p = c ∧ ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, inner Real v (D x) = inner Real v x) ∧
      (∀ x, inner Real v x = c -> D x = x) ∧
      (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - c| ≤ R} ∧
        ∀ x ∉ K, D x = x) ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p)) ∧
      ∃ ε : Real, 0 < ε ∧ ε < R ∧
        ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
          T.source = univ ×ˢ Ioo (-ε) ε ∧
          ContMDiffOn Iprod (𝓡 2) ∞ T T.source ∧
          ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target ∧
          range (fun q : S1 => T (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
          ∃ γ : S1 -> Hemisphere.Plane v,
            _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ ∧
            (∀ q t, t ∈ Ioo (-ε) ε ->
              D (f (T (q, t))) = (c + t) • v + (γ q : E3)) ∧
            ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
              (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
              A '' sphere (0 : Hemisphere.Plane v) 1 = range γ ∧
              ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
                range (fun p => D (f p)) =
                  (fun p => D (f p)) '' range (fun q : S1 => T (q, 0)) ∧
              ∃ a : Real, 0 < a ∧ a < ε / 4 ∧ a < R / 4 ∧
                ∃ s : Real, ∃ hs : 0 < s, s < a / 8 ∧
                ∃ eMinus ePlus : OpenPartialHomeomorph E2 S2,
                  closedBall 0 1 ⊆ eMinus.source ∧ closedBall 0 1 ⊆ ePlus.source ∧
                  ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus eMinus.source ∧
                  ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus.symm eMinus.target ∧
                  ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus ePlus.source ∧
                  ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus.symm ePlus.target ∧
                  Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1) ∧
                  eMinus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, -a)) ∧
                  ePlus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, a)) ∧
                  eMinus '' closedBall 0 1 ∪ T '' (univ ×ˢ Icc (-a) a) ∪
                    ePlus '' closedBall 0 1 = univ ∧
                  T '' (univ ×ˢ Icc (-a) a) =
                    (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ ∧
                  ∃ dMinus dPlus : OpenPartialHomeomorph E2 S2,
                    closedBall 0 1 ⊆ dMinus.source ∧ closedBall 0 1 ⊆ dPlus.source ∧
                    ContMDiffOn (𝓡 2) (𝓡 2) ∞ dMinus dMinus.source ∧
                    ContMDiffOn (𝓡 2) (𝓡 2) ∞ dMinus.symm dMinus.target ∧
                    ContMDiffOn (𝓡 2) (𝓡 2) ∞ dPlus dPlus.source ∧
                    ContMDiffOn (𝓡 2) (𝓡 2) ∞ dPlus.symm dPlus.target ∧
                    dMinus '' closedBall 0 1 = (eMinus '' ball 0 1)ᶜ ∧
                    dMinus '' ball 0 1 = (eMinus '' closedBall 0 1)ᶜ ∧
                    dPlus '' closedBall 0 1 = (ePlus '' ball 0 1)ᶜ ∧
                    dPlus '' ball 0 1 = (ePlus '' closedBall 0 1)ᶜ ∧
                    ∃ gMinus gPlus : E2 -> E3,
                      ContDiff Real ∞ gMinus ∧ ContDiff Real ∞ gPlus ∧
                      Injective gMinus ∧ Injective gPlus ∧
                      (∀ x, Injective (fderiv Real gMinus x)) ∧
                      (∀ x, Injective (fderiv Real gPlus x)) ∧
                      (∀ x, |inner Real v (gMinus x) - (c - a)| < a / 2) ∧
                      (∀ x, |inner Real v (gPlus x) - (c + a)| < a / 2) ∧
                      gMinus '' closedBall (0 : E2) 1 =
                        Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv (c - a) s hs.ne' A ''
                          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                            {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
                      gPlus '' closedBall (0 : E2) 1 =
                        Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv (c + a) (-s)
                          (neg_ne_zero.mpr hs.ne') A ''
                          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
                            {p : S2 | 0 ≤ inner Real v (p : E3)}) ∧
                      ∃ fMinus fPlus : S2 -> E3,
                        _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fMinus ∧
                        _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fPlus ∧
                        Disjoint (range fMinus) (range fPlus) ∧
                        (∀ x ∈ closedBall 0 1, fMinus (dMinus x) = gMinus x) ∧
                        (∀ x ∈ closedBall 0 1, fPlus (dPlus x) = gPlus x) ∧
                        (∀ y ∈ eMinus '' closedBall 0 1, fMinus y = D (f y)) ∧
                        (∀ y ∈ ePlus '' closedBall 0 1, fPlus y = D (f y)) ∧
                        range fMinus = gMinus '' closedBall 0 1 ∪
                          (fun p => D (f p)) '' (eMinus '' closedBall 0 1) ∧
                        range fPlus = gPlus '' closedBall 0 1 ∪
                          (fun p => D (f p)) '' (ePlus '' closedBall 0 1) ∧
                        (∀ t ∈ Icc (-(2 * a)) (2 * a),
                          ((fun x : Hemisphere.Plane v => (c + t) • v + (A x : E3)) ''
                            closedBall 0 1) ∩ range (fun p => D (f p)) =
                              (fun p => D (f p)) '' range (fun q : S1 => T (q, t))) := by
  obtain ⟨p, hp, D, hDheight, hDplane, hDsupport, hDf,
    ε, hε, hεR, T, hsource, hT, hTi, hcenter,
    γ, hγ, hcylinder, A, hboundary, hintersection⟩ :=
    exists_prepared_innermost_regular_circle_of_smooth hf hh hv hheight c hc hne hR
  obtain ⟨a, ha, haε, hsurgery⟩ := exists_two_sided_surgery_of_cylindrical_tube
    hDf hv c hε T hT hTi hsource γ hγ hcylinder A hboundary hintersection
  exact ⟨p, hp, D, hDheight, hDplane, hDsupport, hDf,
    ε, hε, hεR, T, hsource, hT, hTi, hcenter,
    γ, hγ, hcylinder, A, hboundary, hintersection, a, ha, haε, by linarith, hsurgery⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
