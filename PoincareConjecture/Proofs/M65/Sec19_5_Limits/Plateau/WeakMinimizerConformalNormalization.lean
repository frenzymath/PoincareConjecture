import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalClass
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.ThreePointNormalization
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter Complex Metric
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture

private theorem m65Disk_change_globalize (φ : LoopPlane → LoopPlane)
    (hφ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 φ z) :
    ∃ Φ : LoopPlane → LoopPlane, ContDiff ℝ 1 Φ ∧
      ∀ z ∈ loopDiskSet, Φ =ᶠ[𝓝 z] φ := by
  let U := {z | ContDiffAt ℝ 1 φ z}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr
    (fun z hz => (show ContDiffAt ℝ 1 φ z from hz).eventually (by norm_num))
  have hd : Disjoint Uᶜ loopDiskSet := by
    rw [disjoint_left]
    intro z hzU hz
    exact hzU (hφ z hz)
  obtain ⟨χ, hzero, hone, _hχrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓡 2) hU.isClosed_compl isClosed_closedBall hd (n := 1)
  let Φ := fun z => χ z • φ z
  have hχ : ContDiff ℝ 1 χ := χ.contMDiff.contDiff
  refine ⟨Φ, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ U
    · exact hχ.contDiffAt.smul hz
    · apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : LoopPlane => (0 : LoopPlane)) z)
        |>.congr_of_eventuallyEq
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hz)] with w hw
      simp only [Φ, hw, zero_smul]
  · intro z hz
    filter_upwards [hone.filter_mono (nhds_le_nhdsSet hz)] with w hw
    simp only [Φ, hw, one_smul]

private theorem m65Weak_holomorphic_columns (φ : ℂ → ℂ) (z : LoopPlane)
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

private theorem m65Weak_energy_conformal_columns {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (d : Fin 2 → EuclideanSpace ℝ (Fin N))
    (A : LoopPlane →L[ℝ] LoopPlane) (a b : ℝ)
    (h0 : A (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      a • EuclideanSpace.basisFun (Fin 2) ℝ 0 + b • EuclideanSpace.basisFun (Fin 2) ℝ 1)
    (h1 : A (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -b • EuclideanSpace.basisFun (Fin 2) ℝ 0 + a • EuclideanSpace.basisFun (Fin 2) ℝ 1) :
    (1 / 2 : ℝ) * ∑ i : Fin 2,
      H (∑ j : Fin 2, (A (EuclideanSpace.basisFun (Fin 2) ℝ i)) j • d j)
        (∑ j : Fin 2, (A (EuclideanSpace.basisFun (Fin 2) ℝ i)) j • d j) =
      |A.det| * ((1 / 2 : ℝ) * ∑ i : Fin 2, H (d i) (d i)) := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  have hdet : A.det = a ^ 2 + b ^ 2 := by
    change LinearMap.det A.toLinearMap = _
    rw [← LinearMap.det_toMatrix B.toBasis, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis]
    change (A (B 0)) 0 * (A (B 1)) 1 - (A (B 1)) 0 * (A (B 0)) 1 = _
    dsimp only [B]
    rw [h0, h1]
    norm_num [EuclideanSpace.basisFun_apply]
    ring
  rw [hdet, abs_of_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  simp only [Fin.sum_univ_two]
  rw [h0, h1]
  simp only [PiLp.add_apply, PiLp.smul_apply]
  norm_num [EuclideanSpace.basisFun_apply]
  ring

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
  {γ : LoopCircle → M}

theorem m65WeakDisk_holomorphic_change (g : RiemannianMetric 3 M)
    (he : Continuous e)
    (hγ : Continuous γ) (F : M65WeakDisk e γ) (φ ψ : ℂ → ℂ)
    (hφ : ∀ z, ‖z‖ ≤ 1 → ContDiffAt ℂ ∞ φ z)
    (hψ : ∀ z, ‖z‖ ≤ 1 → ContDiffAt ℂ ∞ ψ z)
    (hφdisk : ∀ z, ‖z‖ ≤ 1 → ‖φ z‖ ≤ 1)
    (hψdisk : ∀ z, ‖z‖ ≤ 1 → ‖ψ z‖ ≤ 1)
    (hφcircle : ∀ z, ‖z‖ = 1 → ‖φ z‖ = 1)
    (hψcircle : ∀ z, ‖z‖ = 1 → ‖ψ z‖ = 1)
    (hleft : ∀ z, ‖z‖ ≤ 1 → ψ (φ z) = z)
    (hright : ∀ z, ‖z‖ ≤ 1 → φ (ψ z) = z) :
    ∃ G : M65WeakDisk e γ, G.energy g = F.energy g ∧
      ∀ z w : LoopCircle,
        w.val = orthonormalBasisOneI.repr (φ (orthonormalBasisOneI.repr.symm z)) →
          G.parameter z = F.parameter w := by
  let E := orthonormalBasisOneI.repr
  let φP := fun z : LoopPlane => E (φ (E.symm z))
  let ψP := fun z : LoopPlane => E (ψ (E.symm z))
  have hnorm (z : LoopPlane) : ‖E.symm z‖ = ‖z‖ := E.symm.norm_map z
  have hφP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 φP z := by
    have hh : ContDiffAt ℝ 1 φ (E.symm z) :=
      ((hφ _ ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz))).restrict_scalars ℝ).of_le
        (by simp)
    exact E.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (hh.comp z E.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  have hψP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 ψP z := by
    have hh : ContDiffAt ℝ 1 ψ (E.symm z) :=
      ((hψ _ ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz))).restrict_scalars ℝ).of_le
        (by simp)
    exact E.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (hh.comp z E.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  obtain ⟨Φ, hΦ, hΦeq⟩ := m65Disk_change_globalize φP hφP
  have heq (z : LoopPlane) (hz : z ∈ loopDiskSet) : Φ z = φP z :=
    (hΦeq z hz).self_of_nhds
  have hΦdisk : MapsTo Φ loopDiskSet loopDiskSet := by
    intro z hz
    rw [heq z hz]
    apply mem_closedBall_zero_iff.mpr
    simpa only [φP, E.norm_map] using hφdisk (E.symm z)
      ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz))
  have hΨdisk : MapsTo ψP loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    simpa only [ψP, E.norm_map] using hψdisk (E.symm z)
      ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz))
  have hΦcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖Φ z‖ = 1 := by
    rw [heq z (mem_closedBall_zero_iff.mpr hz.le)]
    simpa only [φP, E.norm_map] using hφcircle (E.symm z) ((hnorm z).trans hz)
  have hΨcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖ψP z‖ = 1 := by
    simpa only [ψP, E.norm_map] using hψcircle (E.symm z) ((hnorm z).trans hz)
  have hleftP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ψP (Φ z) = z := by
    rw [heq z hz]
    dsimp only [φP, ψP]
    rw [E.symm_apply_apply, hleft _ ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz)),
      E.apply_symm_apply]
  have hrightP (z : LoopPlane) (hz : z ∈ loopDiskSet) : Φ (ψP z) = z := by
    rw [heq (ψP z) (hΨdisk hz)]
    dsimp only [φP, ψP]
    rw [E.symm_apply_apply, hright _ ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz)),
      E.apply_symm_apply]
  obtain ⟨G, hvalue, hparameter, hderivative⟩ := m65WeakDisk_smooth_change he hγ F
    Φ ψP hΦ hψP hΦdisk hΨdisk hΦcircle hΨcircle hleftP hrightP
  refine ⟨G, ?_, ?_⟩
  · let ED := m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z)
    have hdensity : m65EmbeddedEnergyDensity g e G.value (fun i z => G.derivative i z)
        =ᵐ[volume.restrict loopDiskSet] fun z => |(fderiv ℝ Φ z).det| • ED (Φ z) := by
      filter_upwards [ae_restrict_mem measurableSet_closedBall,
        ae_all_iff.mpr hderivative] with z hz hdz
      have hdiff : fderiv ℝ Φ z = fderiv ℝ φP z := (hΦeq z hz).fderiv_eq
      obtain ⟨h0, h1⟩ := m65Weak_holomorphic_columns φ z
        ((hφ _ ((hnorm z).trans_le (mem_closedBall_zero_iff.mp hz))).differentiableAt (by simp))
      change _ = _ at h0 h1
      change (1 / 2 : ℝ) * ∑ i : Fin 2,
        m65EmbeddingMetric g e (G.value z) (G.derivative i z) (G.derivative i z) = _
      simp_rw [hdz, hvalue]
      exact m65Weak_energy_conformal_columns (m65EmbeddingMetric g e (F.value (Φ z)))
        (fun i => F.derivative i (Φ z)) (fderiv ℝ Φ z) _ _
        (hdiff ▸ h0) (hdiff ▸ h1)
    have hinjΦ : InjOn Φ loopDiskSet := by
      intro x hx y hy hxy
      exact (hleftP x hx).symm.trans ((congrArg ψP hxy).trans (hleftP y hy))
    have himage : Φ '' loopDiskSet = loopDiskSet := by
      apply Subset.antisymm hΦdisk.image_subset
      intro z hz
      exact ⟨ψP z, hΨdisk hz, hrightP z hz⟩
    change (∫ z in loopDiskSet,
      m65EmbeddedEnergyDensity g e G.value (fun i z => G.derivative i z) z) = _
    calc
      _ = ∫ z in loopDiskSet, |(fderiv ℝ Φ z).det| • ED (Φ z) := integral_congr_ae hdensity
      _ = ∫ z in Φ '' loopDiskSet, ED z :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
          (fun z _ => (hΦ.differentiable one_ne_zero z).hasFDerivAt.hasFDerivWithinAt)
          hinjΦ ED).symm
      _ = F.energy g := by rw [himage]; rfl
  · intro z w hw
    rw [hparameter z]
    apply congrArg F.parameter
    apply Subtype.ext
    exact (heq z (mem_closedBall_zero_iff.mpr z.property.le)).trans hw.symm

theorem m65WeakDisk_conformal_normalization (g : RiemannianMetric 3 M)
    (he : Continuous e) (hγ : Continuous γ) (F : M65WeakDisk e γ)
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ G : M65WeakDisk e γ, G.energy g = F.energy g ∧ G.Normalized a b c := by
  obtain ⟨p, hp⟩ := F.weakly_monotone.surjective a
  obtain ⟨q, hq⟩ := F.weakly_monotone.surjective b
  obtain ⟨r, hr⟩ := F.weakly_monotone.surjective c
  let E := orthonormalBasisOneI.repr
  let P := E.symm p.val
  let Q := E.symm q.val
  let R := E.symm r.val
  have hnorm (z : LoopCircle) : ‖E.symm z.val‖ = 1 := (E.symm.norm_map z.val).trans z.property
  have hpq : P ≠ Q := by
    intro hh
    have heq : p = q := Subtype.ext (E.symm.injective hh)
    exact hab (hp.symm.trans ((congrArg F.parameter heq).trans hq))
  have hpr : P ≠ R := by
    intro hh
    have heq : p = r := Subtype.ext (E.symm.injective hh)
    exact hac (hp.symm.trans ((congrArg F.parameter heq).trans hr))
  have hqr : Q ≠ R := by
    intro hh
    have heq : q = r := Subtype.ext (E.symm.injective hh)
    exact hbc (hq.symm.trans ((congrArg F.parameter heq).trans hr))
  obtain ⟨φ, ψ, hφdisk, hψdisk, hφcircle, hψcircle, hleft, hright,
      hφ, hψ, hP, hQ, hR⟩ :=
    exists_plateau_threePoint_normalization (hnorm p) (hnorm q) (hnorm r) hpq hpr hqr
  obtain ⟨G, henergy, hparameter⟩ := m65WeakDisk_holomorphic_change g he hγ F ψ φ
    hψ hφ hψdisk hφdisk hψcircle hφcircle hright hleft
  refine ⟨G, henergy, ?_⟩
  let oneP : LoopCircle := ⟨E 1, by simp⟩
  let negP : LoopCircle := ⟨E (-1), by simp⟩
  let ip : LoopCircle := ⟨E I, by simp⟩
  let im : LoopCircle := ⟨E (-I), by simp⟩
  change G.parameter oneP = a ∧ G.parameter negP = b ∧
    (G.parameter ip = c ∨ G.parameter im = c)
  refine ⟨?_, ?_, ?_⟩
  · apply (hparameter oneP p ?_).trans hp
    change p.val = E (ψ (E.symm (E 1)))
    rw [E.symm_apply_apply, ← hP, hleft _ (hnorm p).le]
    exact (E.apply_symm_apply p.val).symm
  · apply (hparameter negP q ?_).trans hq
    change q.val = E (ψ (E.symm (E (-1))))
    rw [E.symm_apply_apply, ← hQ, hleft _ (hnorm q).le]
    exact (E.apply_symm_apply q.val).symm
  · rcases hR with hR | hR
    · apply Or.inl
      apply (hparameter ip r ?_).trans hr
      change r.val = E (ψ (E.symm (E I)))
      rw [E.symm_apply_apply, ← hR, hleft _ (hnorm r).le]
      exact (E.apply_symm_apply r.val).symm
    · apply Or.inr
      apply (hparameter im r ?_).trans hr
      change r.val = E (ψ (E.symm (E (-I))))
      rw [E.symm_apply_apply, ← hR, hleft _ (hnorm r).le]
      exact (E.apply_symm_apply r.val).symm

theorem M65WeakDisk.normalized_minimum_is_minimum (g : RiemannianMetric 3 M)
    (he : Continuous e) (hγ : Continuous γ) (F : M65WeakDisk e γ)
    {a b c : LoopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hF : F.MinimizesNormalizedEnergy g a b c) : F.MinimizesEnergy g := by
  intro G
  obtain ⟨G', henergy, hpin⟩ := m65WeakDisk_conformal_normalization g he hγ G a b c hab hac hbc
  exact (hF.2 G' hpin).trans_eq henergy

end PoincareConjecture
