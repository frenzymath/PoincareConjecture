import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ClosedStripDifferential
import PoincareConjecture.Proofs.M64.Mathlib.LogScaledAffineDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

theorem annulus_strip_gram_pos (A : M64Annulus g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {p : LoopPlane} (hp : p ∈ m64AnnulusOpenStrip) :
    0 < m60AreaGram g A.map p 0 0 := by
  have hWS : m64AnnulusOpenStrip ⊆ S := fun _ h => ⟨h.1.le, h.2.le⟩
  have hnh : S ∈ 𝓝 p := mem_of_superset (isOpen_m64AnnulusOpenStrip.mem_nhds hp) hWS
  have hd := annulus_strip_within_injective A hAc hinj p (hWS hp)
  rw [mfderivWithin_of_mem_nhds hnh] at hd
  have hne : mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≠ 0 := by
    intro hz
    have hb := hd (hz.trans (map_zero _).symm)
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 0 hb
  exact g.pos (A.map p) _ hne

theorem annulus_strip_energy_eq (A : M64Annulus g c0 c1) (r : ℝ)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {p : LoopPlane} (hp : p ∈ m64AnnulusOpenStrip) :
    m64ModulusEnergyDensity g r A.map p = r * m60AreaGram g A.map p 0 0 := by
  have hWS : m64AnnulusOpenStrip ⊆ S := fun _ h => ⟨h.1.le, h.2.le⟩
  have hnh : S ∈ 𝓝 p := mem_of_superset (isOpen_m64AnnulusOpenStrip.mem_nhds hp) hWS
  have hc := (annulus_strip_within_conformal A r hAc
    (hAi.mono (fun _ h => h 1 (mem_univ _))) hconf p (hWS hp)).1
  rw [mfderivWithin_of_mem_nhds hnh] at hc
  change r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 at hc
  unfold m64ModulusEnergyDensity
  rw [← hc]
  ring

theorem annulus_strip_log_energy (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {p : LoopPlane} (hp : p ∈ m64AnnulusOpenStrip) (v : LoopPlane) :
    fderiv ℝ (fun q => Real.log (m64ModulusEnergyDensity g r A.map q)) p v =
      fderiv ℝ (fun q => Real.log (m60AreaGram g A.map q 0 0)) p v := by
  have hEq : m64ModulusEnergyDensity g r A.map =ᶠ[𝓝 p]
      fun q => r * m60AreaGram g A.map q 0 0 := by
    filter_upwards [isOpen_m64AnnulusOpenStrip.mem_nhds hp] with q hq
    exact annulus_strip_energy_eq A r hAc hAi hconf hq
  have hd := (m64AreaGram_entry_contDiffAt (g := g)
    (hAi.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hp)) 0 0).differentiableAt
      (by simp)
  simpa only [zero_add, ContinuousLinearEquiv.refl_apply] using
    log_scaled_affine_derivative (ContinuousLinearEquiv.refl ℝ LoopPlane) 0 hr.ne'
      (by simpa only [zero_add, ContinuousLinearEquiv.refl_apply] using hd)
      (by simpa only [zero_add, ContinuousLinearEquiv.refl_apply] using
        (annulus_strip_gram_pos A hAc hinj hp).ne')
      (by simpa only [zero_add, ContinuousLinearEquiv.refl_apply] using hEq) v

end PoincareConjecture.M64
