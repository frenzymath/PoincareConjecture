import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSmoothingConvolution
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerEnergyContinuity
import PoincareConjecture.Proofs.M60.Mathlib.NonNullSmoothingChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter ContinuousLinearMap
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ}

def suBlendJet (rho : LoopPlane → ℝ) (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (z : LoopPlane) (a : EuclideanSpace ℝ (Fin n))
    (L : LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (1 - rho z) • fderiv ℝ u z + rho z • L +
    (fderiv ℝ rho z).smulRight (a - u z)

theorem suBlendJet_fderiv
    {rho : LoopPlane → ℝ} {u v : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {z : LoopPlane} (hrho : DifferentiableAt ℝ rho z)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    fderiv ℝ (M40.cutoffBlend rho u v) z =
      suBlendJet rho u z (v z) (fderiv ℝ v z) := by
  have hd := ((hrho.hasFDerivAt.const_sub 1).smul hu.hasFDerivAt).add
    (hrho.hasFDerivAt.smul hv.hasFDerivAt)
  have heq : M40.cutoffBlend rho u v = fun y => (1 - rho y) • u y + rho y • v y := by
    funext y
    dsimp [M40.cutoffBlend]
    module
  rw [heq]
  change fderiv ℝ ((fun x => 1 - rho x) • u + rho • v) z = _
  rw [hd.fderiv]
  ext w j
  simp only [suBlendJet, add_apply, smul_apply, smulRight_apply, neg_apply,
    PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
  ring

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def suBlendEnergyObservable (g : RiemannianMetric n M) (b : M)
    (rho : LoopPlane → ℝ) (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (q : LoopPlane × (EuclideanSpace ℝ (Fin n) ×
      (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n)))) : ℝ :=
  ((1 / 2 : ℝ) * ∑ i : Fin 2,
    g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      ((1 - rho q.1) • u q.1 + rho q.1 • q.2.1)
      (suBlendJet rho u q.1 q.2.1 q.2.2 (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (suBlendJet rho u q.1 q.2.1 q.2.2 (EuclideanSpace.basisFun (Fin 2) ℝ i))) /
        (16 / (‖q.1‖ ^ 2 + 4) ^ 2)

theorem suBlendEnergyObservable_self (g : RiemannianMetric n M) (b : M)
    (rho : LoopPlane → ℝ) (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane) :
    suBlendEnergyObservable g b rho u (z, u z, fderiv ℝ u z) =
      ((1 / 2 : ℝ) * ∑ i : Fin 2,
        g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (u z)
          (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))) /
            (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  have hv : (1 - rho z) • u z + rho z • u z = u z := by module
  have hd : suBlendJet rho u z (u z) (fderiv ℝ u z) = fderiv ℝ u z := by
    unfold suBlendJet
    simp only [sub_self, smulRight_zero, add_zero]
    module
  simp only [suBlendEnergyObservable, hv, hd]

theorem suBlendEnergyObservable_continuousAt
    (g : RiemannianMetric n M) (b : M)
    {rho : LoopPlane → ℝ} {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {z : LoopPlane} (hrho : ContDiffAt ℝ 1 rho z) (hu : ContDiffAt ℝ 1 u z)
    (hz : u z ∈ (extChartAt (𝓡 n) b).target) :
    ContinuousAt (suBlendEnergyObservable g b rho u) (z, u z, fderiv ℝ u z) := by
  let q := (z, u z, fderiv ℝ u z)
  have hr : ContinuousAt (fun q : LoopPlane × (EuclideanSpace ℝ (Fin n) ×
      (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) => rho q.1) q :=
    hrho.continuousAt.comp continuousAt_fst
  have hu0 := hu.continuousAt.comp (continuousAt_fst (p := q))
  have hu1 := (hu.continuousAt_fderiv one_ne_zero).comp (continuousAt_fst (p := q))
  have hr1 := (hrho.continuousAt_fderiv one_ne_zero).comp (continuousAt_fst (p := q))
  have hv := ((continuousAt_const (y := (1 : ℝ))).sub hr).smul hu0 |>.add
    (hr.smul continuousAt_snd.fst)
  have hB := ((g.contDiffOn_chartCoefficients b).contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hz)).continuousAt
  have hvalue : (1 - rho z) • u z + rho z • u z = u z := by module
  have hBbase : ContinuousAt (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ((1 - rho z) • u z + rho z • u z) := by
    rw [hvalue]
    exact hB
  have hB' : ContinuousAt (fun q : LoopPlane × (EuclideanSpace ℝ (Fin n) ×
      (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) =>
      g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
        ((1 - rho q.1) • u q.1 + rho q.1 • q.2.1)) q := by
    exact hBbase.comp (f := fun q : LoopPlane × (EuclideanSpace ℝ (Fin n) ×
      (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) =>
        (1 - rho q.1) • u q.1 + rho q.1 • q.2.1) hv
  have hd : ContinuousAt (fun q => suBlendJet rho u q.1 q.2.1 q.2.2) q := by
    apply (((continuousAt_const (y := (1 : ℝ))).sub hr).smul hu1).add
      (hr.smul continuousAt_snd.snd) |>.add
    exact ((smulRightL ℝ LoopPlane (EuclideanSpace ℝ (Fin n))).continuous₂.continuousAt).comp
      (hr1.prodMk (continuousAt_snd.fst.sub hu0))
  have hcol (i : Fin 2) := hd.clm_apply
    (continuousAt_const (y := EuclideanSpace.basisFun (Fin 2) ℝ i))
  have hsum := (continuousAt_const (y := (1 / 2 : ℝ))).mul
    (((hB'.clm_apply (hcol 0)).clm_apply (hcol 0)).add
      ((hB'.clm_apply (hcol 1)).clm_apply (hcol 1)))
  have hfactor : ContinuousAt (fun q : LoopPlane × (EuclideanSpace ℝ (Fin n) ×
      (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) => 16 / (‖q.1‖ ^ 2 + 4) ^ 2) q :=
    continuousAt_const.div
      (((continuousAt_fst.norm.pow 2).add continuousAt_const).pow 2) (by positivity)
  unfold suBlendEnergyObservable
  have hh := hsum.div hfactor
    (show (16 : ℝ) / (‖q.1‖ ^ 2 + 4) ^ 2 ≠ 0 by positivity)
  convert hh using 1
  ext y
  simp only [Fin.sum_univ_two, Pi.mul_apply, Pi.add_apply, Pi.div_apply]

end PoincareConjecture.M60

end
