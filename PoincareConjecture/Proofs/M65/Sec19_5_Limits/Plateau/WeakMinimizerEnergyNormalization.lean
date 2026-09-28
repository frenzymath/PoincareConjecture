import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryNormalization
import PoincareConjecture.Definitions.M60Area

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric Complex
open scoped Manifold ContDiff Topology ENNReal Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

private theorem m65Holomorphic_real_columns (φ : ℂ → ℂ) (z : LoopPlane)
    (hφ : DifferentiableAt ℂ φ (orthonormalBasisOneI.repr.symm z)) :
    let e := orthonormalBasisOneI.repr
    let B := EuclideanSpace.basisFun (Fin 2) ℝ
    let A := fderiv ℝ (fun w : LoopPlane => e (φ (e.symm w))) z
    let c := deriv φ (e.symm z)
    A (B 0) = c.re • B 0 + c.im • B 1 ∧
      A (B 1) = -c.im • B 0 + c.re • B 1 := by
  let e := orthonormalBasisOneI.repr
  have hd := e.toContinuousLinearEquiv.hasFDerivAt.comp z
    ((hφ.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp z
      e.symm.toContinuousLinearEquiv.hasFDerivAt)
  dsimp only
  erw [hd.fderiv]
  constructor <;> ext i <;> fin_cases i <;>
    simp [e, Complex.orthonormalBasisOneI_repr_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply, EuclideanSpace.basisFun_apply]

private theorem m65EnergyDensity_comp_columns (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (φ : LoopPlane → LoopPlane) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f (φ z))
    (hφ : DifferentiableAt ℝ φ z) (a b : ℝ)
    (h0 : fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      a • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        b • EuclideanSpace.basisFun (Fin 2) ℝ 1)
    (h1 : fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -b • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        a • EuclideanSpace.basisFun (Fin 2) ℝ 1) :
    m60EnergyDensity g (f ∘ φ) z =
      |(fderiv ℝ φ z).det| * m60EnergyDensity g f (φ z) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  let D := mfderiv (𝓡 2) (𝓡 3) f (φ z)
  let A := fderiv ℝ φ z
  have hdet : A.det = a ^ 2 + b ^ 2 := by
    change LinearMap.det A.toLinearMap = _
    rw [← LinearMap.det_toMatrix B.toBasis, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis]
    change (A (B 0)) 0 * (A (B 1)) 1 - (A (B 1)) 0 * (A (B 0)) 1 = _
    dsimp only [A, B]
    rw [h0, h1]
    norm_num [EuclideanSpace.basisFun_apply]
    ring
  have he (F : LoopPlane → M) (w : LoopPlane) :
      m60EnergyDensity g F w = (1 / 2 : ℝ) *
        (inner ℝ (mfderiv (𝓡 2) (𝓡 3) F w (B 0))
          (mfderiv (𝓡 2) (𝓡 3) F w (B 0)) +
        inner ℝ (mfderiv (𝓡 2) (𝓡 3) F w (B 1))
          (mfderiv (𝓡 2) (𝓡 3) F w (B 1))) := by
    simp only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two]
    rfl
  rw [he, he, hdet, abs_of_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  simp only [mfderiv_comp z hf hφ.mdifferentiableAt, mfderiv_eq_fderiv]
  change (1 / 2 : ℝ) * (inner ℝ (D (A (B 0))) (D (A (B 0))) +
    inner ℝ (D (A (B 1))) (D (A (B 1)) )) = _
  simp only [A, B, h0, h1, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem m65EnergyDensity_comp_holomorphic (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (φ : ℂ → ℂ) (z : LoopPlane)
    (hφ : DifferentiableAt ℂ φ (orthonormalBasisOneI.repr.symm z))
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f
      (orthonormalBasisOneI.repr (φ (orthonormalBasisOneI.repr.symm z)))) :
    let Φ := fun w : LoopPlane =>
      orthonormalBasisOneI.repr (φ (orthonormalBasisOneI.repr.symm w))
    m60EnergyDensity g (f ∘ Φ) z =
      |(fderiv ℝ Φ z).det| * m60EnergyDensity g f (Φ z) := by
  let e := orthonormalBasisOneI.repr
  let Φ := fun w : LoopPlane => e (φ (e.symm w))
  have hΦ : DifferentiableAt ℝ Φ z :=
    e.toContinuousLinearEquiv.differentiableAt.comp z
      ((hφ.restrictScalars ℝ).comp z e.symm.toContinuousLinearEquiv.differentiableAt)
  obtain ⟨h0, h1⟩ := m65Holomorphic_real_columns φ z hφ
  exact m65EnergyDensity_comp_columns g f Φ z hf hΦ _ _ h0 h1

theorem m65DiskEnergy_holomorphic_reparameterize {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ)
    (henergy : IntegrableOn (m60EnergyDensity g D.map) loopDiskSet volume)
    (φ ψ : ℂ → ℂ)
    (hφ : ∀ z, ‖z‖ ≤ 1 → ContDiffAt ℂ ∞ φ z)
    (hψ : ∀ z, ‖z‖ ≤ 1 → ContDiffAt ℂ ∞ ψ z)
    (hφdisk : ∀ z, ‖z‖ ≤ 1 → ‖φ z‖ ≤ 1)
    (hψdisk : ∀ z, ‖z‖ ≤ 1 → ‖ψ z‖ ≤ 1)
    (hleft : ∀ z, ‖z‖ ≤ 1 → ψ (φ z) = z)
    (hright : ∀ z, ‖z‖ ≤ 1 → φ (ψ z) = z) :
    let Φ := fun w : LoopPlane =>
      orthonormalBasisOneI.repr (φ (orthonormalBasisOneI.repr.symm w))
    IntegrableOn (m60EnergyDensity g (D.map ∘ Φ)) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m60EnergyDensity g (D.map ∘ Φ) z) =
        ∫ z in loopDiskSet, m60EnergyDensity g D.map z := by
  let e := orthonormalBasisOneI.repr
  let Φ := fun w : LoopPlane => e (φ (e.symm w))
  let Ψ := fun w : LoopPlane => e (ψ (e.symm w))
  have he (z : LoopPlane) (hz : z ∈ loopDiskSet) : ‖e.symm z‖ ≤ 1 := by
    rw [e.symm.norm_map]
    exact mem_closedBall_zero_iff.mp hz
  have hΦdisk : MapsTo Φ loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    simpa only [Φ, e.norm_map] using hφdisk (e.symm z) (he z hz)
  have hΨdisk : MapsTo Ψ loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    simpa only [Ψ, e.norm_map] using hψdisk (e.symm z) (he z hz)
  have hleftP (z : LoopPlane) (hz : z ∈ loopDiskSet) : Ψ (Φ z) = z := by
    dsimp only [Φ, Ψ]
    rw [e.symm_apply_apply, hleft _ (he z hz), e.apply_symm_apply]
  have hrightP (z : LoopPlane) (hz : z ∈ loopDiskSet) : Φ (Ψ z) = z := by
    dsimp only [Φ, Ψ]
    rw [e.symm_apply_apply, hright _ (he z hz), e.apply_symm_apply]
  have hΦ (z : LoopPlane) (hz : z ∈ loopDiskSet) : DifferentiableAt ℝ Φ z :=
    e.toContinuousLinearEquiv.differentiableAt.comp z
      (((hφ _ (he z hz)).differentiableAt (by simp)).restrictScalars ℝ |>.comp z
        e.symm.toContinuousLinearEquiv.differentiableAt)
  have hΨ (z : LoopPlane) (hz : z ∈ loopDiskSet) : DifferentiableAt ℝ Ψ z :=
    e.toContinuousLinearEquiv.differentiableAt.comp z
      (((hψ _ (he z hz)).differentiableAt (by simp)).restrictScalars ℝ |>.comp z
        e.symm.toContinuousLinearEquiv.differentiableAt)
  have hs : MeasurableSet loopDiskSet := isClosed_closedBall.measurableSet
  have hinj : InjOn Φ loopDiskSet := by
    intro x hx y hy hxy
    exact (hleftP x hx).symm.trans ((congrArg Ψ hxy).trans (hleftP y hy))
  have himage : Φ '' loopDiskSet = loopDiskSet := by
    apply Subset.antisymm hΦdisk.image_subset
    intro z hz
    exact ⟨Ψ z, hΨdisk hz, hrightP z hz⟩
  have hDpull : ∀ᵐ z ∂volume, z ∈ loopDiskSet →
      MDifferentiableAt (𝓡 2) (𝓡 3) D.map (Φ z) := by
    let N := {y | y ∈ loopDiskSet ∧ ¬MDifferentiableAt (𝓡 2) (𝓡 3) D.map y}
    have hN : volume N = 0 := by
      simpa only [Classical.not_imp, N] using ae_iff.mp D.ae_manifold_differentiable
    have hnull : volume (Ψ '' N) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (fun y hy => (hΨ y hy.1).differentiableWithinAt) hN
    apply ae_iff.mpr
    apply measure_mono_null _ hnull
    intro z hz
    have hz' : z ∈ loopDiskSet ∧ ¬MDifferentiableAt (𝓡 2) (𝓡 3) D.map (Φ z) :=
      Classical.not_imp.mp hz
    exact ⟨Φ z, ⟨hΦdisk hz'.1, hz'.2⟩, hleftP z hz'.1⟩
  have hdensity : m60EnergyDensity g (D.map ∘ Φ) =ᵐ[volume.restrict loopDiskSet]
      fun z => |(fderiv ℝ Φ z).det| • m60EnergyDensity g D.map (Φ z) := by
    filter_upwards [(ae_restrict_iff' hs).mpr hDpull, ae_restrict_mem hs] with z hDz hz
    exact m65EnergyDensity_comp_holomorphic g D.map φ z
      ((hφ _ (he z hz)).differentiableAt (by simp)) hDz
  have hderiv : ∀ z ∈ loopDiskSet,
      HasFDerivWithinAt Φ (fderiv ℝ Φ z) loopDiskSet z :=
    fun z hz => (hΦ z hz).hasFDerivAt.hasFDerivWithinAt
  have hweighted : IntegrableOn
      (fun z => |(fderiv ℝ Φ z).det| • m60EnergyDensity g D.map (Φ z))
      loopDiskSet volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hderiv hinj _).mp
    rw [himage]
    exact henergy
  refine ⟨hweighted.congr hdensity.symm, ?_⟩
  calc
    _ = ∫ z in loopDiskSet,
        |(fderiv ℝ Φ z).det| • m60EnergyDensity g D.map (Φ z) :=
      integral_congr_ae hdensity
    _ = ∫ z in Φ '' loopDiskSet, m60EnergyDensity g D.map z :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv hinj _).symm
    _ = _ := by rw [himage]

theorem m65SpanningDisk_threePointEnergyNormalization {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ)
    (henergy : IntegrableOn (m60EnergyDensity g D.map) loopDiskSet volume)
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
      IntegrableOn (m60EnergyDensity g D'.map) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m60EnergyDensity g D'.map z) =
        (∫ z in loopDiskSet, m60EnergyDensity g D.map z) ∧
      (D'.reparameterization.inverse a).val = orthonormalBasisOneI.repr 1 ∧
      (D'.reparameterization.inverse b).val = orthonormalBasisOneI.repr (-1) ∧
      ((D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr I ∨
        (D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr (-I)) := by
  let e := orthonormalBasisOneI.repr
  let old := fun z : LoopCircle => e.symm (D.reparameterization.inverse z).val
  have hold : Function.Injective old := by
    intro x y hxy
    apply D.reparameterization.right_inverse.injective
    apply Subtype.ext
    exact e.symm.injective hxy
  have hnorm (z : LoopCircle) : ‖old z‖ = 1 := by
    dsimp only [old]
    rw [e.symm.norm_map, (D.reparameterization.inverse z).property]
  obtain ⟨φ, ψ, hφdisk, hψdisk, hφcircle, hψcircle, hleft, hright,
      hφsmooth, hψsmooth, ha, hb, hc⟩ :=
    exists_plateau_threePoint_normalization (hnorm a) (hnorm b) (hnorm c)
      (fun h => hab (hold h)) (fun h => hac (hold h)) (fun h => hbc (hold h))
  let φP := fun z : LoopPlane => e (φ (e.symm z))
  let ψP := fun z : LoopPlane => e (ψ (e.symm z))
  have hnormP (z : LoopPlane) : ‖e.symm z‖ = ‖z‖ := e.symm.norm_map z
  have hφPdisk : MapsTo φP loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    dsimp only [φP]
    rw [e.norm_map]
    exact hφdisk _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))
  have hψPdisk : MapsTo ψP loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    dsimp only [ψP]
    rw [e.norm_map]
    exact hψdisk _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))
  have hφPcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖φP z‖ = 1 := by
    dsimp only [φP]
    rw [e.norm_map]
    exact hφcircle _ ((hnormP z).trans hz)
  have hψPcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖ψP z‖ = 1 := by
    dsimp only [ψP]
    rw [e.norm_map]
    exact hψcircle _ ((hnormP z).trans hz)
  have hleftP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ψP (φP z) = z := by
    dsimp only [φP, ψP]
    rw [e.symm_apply_apply, hleft _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz)),
      e.apply_symm_apply]
  have hrightP (z : LoopPlane) (hz : z ∈ loopDiskSet) : φP (ψP z) = z := by
    dsimp only [φP, ψP]
    rw [e.symm_apply_apply, hright _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz)),
      e.apply_symm_apply]
  have hφP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 φP z := by
    have h : ContDiffAt ℝ 1 φ (e.symm z) :=
      ((hφsmooth _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))).restrict_scalars ℝ).of_le
        (by simp)
    exact e.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (h.comp z e.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  have hψP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 ψP z := by
    have h : ContDiffAt ℝ 1 ψ (e.symm z) :=
      ((hψsmooth _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))).restrict_scalars ℝ).of_le
        (by simp)
    exact e.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (h.comp z e.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  obtain ⟨D', hmap, harea, hboundary⟩ := m65SpanningDisk_reparameterize D ψP φP
    hψP hφP hψPdisk hφPdisk hψPcircle hφPcircle hrightP hleftP
  obtain ⟨henergy', heq⟩ := m65DiskEnergy_holomorphic_reparameterize D henergy ψ φ
    hψsmooth hφsmooth hψdisk hφdisk hright hleft
  have hinverse (z : LoopCircle) : (D'.reparameterization.inverse z).val =
      φP (D.reparameterization.inverse z).val := by
    let w := D'.reparameterization.inverse z
    have hpre : (⟨ψP w, hψPcircle w w.property⟩ : LoopCircle) =
        D.reparameterization.inverse z := by
      apply D.reparameterization.left_inverse.injective
      rw [← hboundary w, D.reparameterization.right_inverse]
      exact D'.reparameterization.right_inverse z
    calc
      _ = φP (ψP w) := (hrightP w (mem_closedBall_zero_iff.mpr w.property.le)).symm
      _ = _ := congrArg φP (congrArg Subtype.val hpre)
  refine ⟨D', harea, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap]
    exact henergy'
  · rw [hmap]
    exact heq
  · rw [hinverse]
    exact congrArg e ha
  · rw [hinverse]
    exact congrArg e hb
  · rw [hinverse]
    exact hc.imp (congrArg e) (congrArg e)

theorem m65SpanningDisk_normalizedEnergyComparison {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)}
    (hcomparison : ∀ (D : LipschitzSpanningDisk g γ) (ε : ℝ), 0 < ε →
      ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
        IntegrableOn (m60EnergyDensity g D'.map) loopDiskSet volume ∧
        (∫ z in loopDiskSet, m60EnergyDensity g D'.map z) ≤ D.area + ε)
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D : LipschitzSpanningDisk g γ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
      IntegrableOn (m60EnergyDensity g D'.map) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m60EnergyDensity g D'.map z) ≤ D.area + ε ∧
      (D'.reparameterization.inverse a).val = orthonormalBasisOneI.repr 1 ∧
      (D'.reparameterization.inverse b).val = orthonormalBasisOneI.repr (-1) ∧
      ((D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr I ∨
        (D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr (-I)) := by
  obtain ⟨D₁, harea₁, henergy₁, hbound⟩ := hcomparison D ε hε
  obtain ⟨D₂, harea₂, henergy₂, heq, ha, hb, hc⟩ :=
    m65SpanningDisk_threePointEnergyNormalization D₁ henergy₁ a b c hab hac hbc
  exact ⟨D₂, harea₂.trans harea₁, henergy₂, heq.trans_le hbound, ha, hb, hc⟩

end PoincareConjecture
