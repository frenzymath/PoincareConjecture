import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusClosedConformality
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusEnergyDensity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem m64ModulusEnergyDensity_contDiffOn
    (r : ℝ) {f : LoopPlane → M} {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O) :
    ContDiffOn ℝ ∞ (m64ModulusEnergyDensity g r f) O := by
  intro p hp
  have hfp := hf.contMDiffAt (hO.mem_nhds hp)
  exact (((contDiffAt_const.mul (m64AreaGram_entry_contDiffAt hfp 0 0)).add
    (contDiffAt_const.mul (m64AreaGram_entry_contDiffAt hfp 1 1))).div_const 2).contDiffWithinAt





theorem m64ModulusEnergyDensity_nonneg (r : ℝ) (hr : 0 ≤ r)
    (f : LoopPlane → M) (p : LoopPlane) : 0 ≤ m64ModulusEnergyDensity g r f p := by
  exact div_nonneg (add_nonneg
    (mul_nonneg hr (m60AreaGram_diagonal_nonneg g f p 0))
    (mul_nonneg (inv_nonneg.mpr hr) (m60AreaGram_diagonal_nonneg g f p 1))) (by norm_num)





theorem m64Annulus_modulus_conformal_on_interior_of_ae
    (A : M64Annulus g c0 c1) (r : ℝ)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusInterior,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
  have hcont (i j : Fin 2) :
      ContinuousOn (fun p => m60AreaGram g A.map p i j) m64AnnulusInterior := by
    intro p hp
    exact (m64AreaGram_entry_contDiffAt
      (hf.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)) i j).continuousAt.continuousWithinAt
  rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior] at hconformal
  have hclosure : m64AnnulusInterior ⊆ closure (interior m64AnnulusInterior) := by
    rw [isOpen_m64AnnulusInterior.interior_eq]
    exact subset_closure
  have hdiag := MeasureTheory.Measure.eqOn_of_ae_eq (hconformal.mono fun _ h => h.1)
    (continuousOn_const.mul (hcont 0 0)) (continuousOn_const.mul (hcont 1 1)) hclosure
  have hcross := MeasureTheory.Measure.eqOn_of_ae_eq (hconformal.mono fun _ h => h.2)
    (hcont 0 1) continuousOn_const hclosure
  exact fun p hp => ⟨hdiag hp, hcross hp⟩





theorem m64Annulus_modulus_conformal_on_domain_of_ae
    (A : M64Annulus g c0 c1) (r : ℝ) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hpoint := m64Annulus_modulus_conformal_on_interior_of_ae A r
    (hf.mono (hsub.trans hdom)) hconformal
  have hcont (i j : Fin 2) :
      ContinuousOn (fun p => m60AreaGram g A.map p i j) m64AnnulusDomain := by
    intro p hp
    exact (m64AreaGram_entry_contDiffAt
      (hf.contMDiffAt (hO.mem_nhds (hdom hp))) i j).continuousAt.continuousWithinAt
  have hclosure : m64AnnulusDomain ⊆ closure m64AnnulusInterior := by
    rw [m64AnnulusInterior_closure]
  have hdiag : EqOn (fun p => r * m60AreaGram g A.map p 0 0)
      (fun p => r⁻¹ * m60AreaGram g A.map p 1 1) m64AnnulusInterior :=
    fun p hp => (hpoint p hp).1
  have hcross : EqOn (fun p => m60AreaGram g A.map p 0 1)
      (fun _ => (0 : ℝ)) m64AnnulusInterior := fun p hp => (hpoint p hp).2
  exact fun p hp => ⟨hdiag.of_subset_closure (continuousOn_const.mul (hcont 0 0))
    (continuousOn_const.mul (hcont 1 1)) hsub hclosure hp,
    hcross.of_subset_closure (hcont 0 1) continuousOn_const hsub hclosure hp⟩





theorem m64Annulus_modulus_conformal_fderiv_on_domain_of_ae
    (A : M64Annulus g c0 c1) (r : ℝ) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusDomain,
      fderiv ℝ (m64ModulusEnergyDensity g r A.map) p =
          fderiv ℝ (fun q => r * m60AreaGram g A.map q 0 0) p ∧
        fderiv ℝ (fun q => m60AreaGram g A.map q 0 1) p = 0 := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hpoint := m64Annulus_modulus_conformal_on_interior_of_ae A r
    (hf.mono (hsub.trans hdom)) hconformal
  have hGram (i j : Fin 2) : ContDiffOn ℝ ∞ (fun q => m60AreaGram g A.map q i j) O :=
    fun p hp => (m64AreaGram_entry_contDiffAt
      (hf.contMDiffAt (hO.mem_nhds hp)) i j).contDiffWithinAt
  have hcont (i j : Fin 2) : ContinuousOn
      (fun p => fderiv ℝ (fun q => m60AreaGram g A.map q i j) p) m64AnnulusDomain :=
    ((hGram i j).fderiv_of_isOpen hO (m := ∞) (by simp)).continuousOn.mono hdom
  have hdiag : EqOn
      (fun p => fderiv ℝ (m64ModulusEnergyDensity g r A.map) p)
      (fun p => fderiv ℝ (fun q => r * m60AreaGram g A.map q 0 0) p)
        m64AnnulusInterior := by
    intro p hp
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hp] with q hq
    unfold m64ModulusEnergyDensity
    rw [← (hpoint q hq).1]
    ring
  have hcross : EqOn
      (fun p => fderiv ℝ (fun q => m60AreaGram g A.map q 0 1) p)
      (fun _ => (0 : LoopPlane →L[ℝ] ℝ)) m64AnnulusInterior := by
    intro p hp
    have heq : (fun q => m60AreaGram g A.map q 0 1) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hp] with q hq
      exact (hpoint q hq).2
    simpa only [fderiv_const_apply] using heq.fderiv_eq (𝕜 := ℝ)
  have hclosure : m64AnnulusDomain ⊆ closure m64AnnulusInterior := by
    rw [m64AnnulusInterior_closure]
  have hE := ((m64ModulusEnergyDensity_contDiffOn (g := g) r hO hf).fderiv_of_isOpen hO
    (m := ∞) (by simp)).continuousOn.mono hdom
  have h00 := (((contDiffOn_const (c := r)).mul (hGram 0 0)).fderiv_of_isOpen hO
    (m := ∞) (by simp)).continuousOn.mono hdom
  exact fun p hp => ⟨hdiag.of_subset_closure hE h00 hsub hclosure hp,
    hcross.of_subset_closure (hcont 0 1) continuousOn_const hsub hclosure hp⟩

end PoincareConjecture
