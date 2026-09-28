import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaInnerData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ShortSectorTemplates











set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_common_beta_shared_short_data
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2) :
    ∃ S : CommonBetaInnerShortData kappa J2 h inner,
      S.beta 0 = kappa (J2.symm
        ((![1, -1, -1, 1] (finProdFinEquiv (inner, (0 : Fin 2)))) / Real.sqrt 2,
          (![1, 1, -1, -1] (finProdFinEquiv (inner, (0 : Fin 2)))) / Real.sqrt 2)) ∧
      MapsTo S.beta (Icc (0 : ℝ) 1)
        (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 6 * h ∧
          |(J2 x).1| ≤ (![1, -1] inner) * (J2 x).2}) := by
  classical
  let sigma : ℝ → ℝ := Real.smoothTransition
  let sign : Fin 2 → ℝ := ![1, -1]
  let rb : ℝ → ℝ := fun t => 1 + 5 * h +
    (t - 5 * h) * (1 - sigma ((t - 4 * h) / (2 * h))) +
    (1 - t - 5 * h) * (1 - sigma ((1 - t - 4 * h) / (2 * h)))
  let ab : ℝ → ℝ := fun t => Real.pi / 4 +
    (Real.pi / 2) * sigma ((t - 4 * h) / (1 - 8 * h))
  let rg : ℝ → ℝ := fun t => 1 + h +
    (2 * h - t) * (1 - sigma ((t - h) / h)) +
    (2 * h - (1 - t)) * (1 - sigma ((1 - t - h) / h))
  let ag : ℝ → ℝ := fun t => 3 * Real.pi / 4 -
    (Real.pi / 2) * sigma ((t - h) / (1 - 2 * h))
  let b : Fin 2 → ℝ → E2 := fun i t => J2.symm
    (sign i * rb t * Real.cos (ab t), sign i * rb t * Real.sin (ab t))
  let g : Fin 2 → ℝ → E2 := fun i t => J2.symm
    (sign i * rg t * Real.cos (ag t), sign i * rg t * Real.sin (ag t))
  have hTemplates := exists_saddle_short_sector_templates
    kappa hkappaSource hkappa hkappaInv J2 hJ2 h hh hsmall
  dsimp only at hTemplates
  obtain ⟨w, N, hw, _hSmooth, _hBounds, hRegular, hGerms, hRange,
    hProper, hJoins, _hBetaDisjoint, _hGammaDisjoint, hNormal⟩ := hTemplates
  let S : CommonBetaInnerShortData kappa J2 h inner := {
    beta := kappa ∘ b inner
    b := b inner
    gamma := kappa ∘ g inner
    g := g inner
    w := w
    hw := hw
    N := N inner
    hBetaDef := rfl
    hGammaDef := rfl
    hBetaData := ⟨(hRegular inner).1, (hRegular inner).2.1,
      (hRegular inner).2.2.1⟩
    hGammaData := (hRegular inner).2.2.2
    hGerms := hGerms inner
    hBetaRange := (hRange inner).1
    hGammaRange := (hRange inner).2
    hBetaProper := (hProper inner).1
    hGammaProper := (hProper inner).2.1
    hBetaCut := fun t ht =>
      ⟨(hProper inner).2.2.1 t ht, (hProper inner).2.2.2.1 t ht⟩
    hGammaCut := (hProper inner).2.2.2.2
    hJoins := hJoins inner
    hNsource := (hNormal inner).1
    hNsubset := (hNormal inner).2.1
    hNtarget := (hNormal inner).2.2.1
    hN := (hNormal inner).2.2.2.1
    hNi := (hNormal inner).2.2.2.2.1
    hNform := (hNormal inner).2.2.2.2.2 }
  refine ⟨S, ?_, ?_⟩
  · have hzero : (0 : ℝ) ∈ Ioo (-h / 8) (1 + h / 8) := by
      constructor <;> linarith
    have hstart := (hGerms inner 0 hzero).1 (by linarith : (0 : ℝ) ≤ 4 * h)
    simpa only [add_zero, one_smul] using hstart
  · intro t ht
    refine ⟨S.b t, S.hBetaRange ht, ?_⟩
    rw [S.hBetaDef]
    rfl

end PoincareConjecture.M25.Topology3D
