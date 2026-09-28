import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSmoothGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m64AnnulusInterior_closure : closure m64AnnulusInterior = m64AnnulusDomain := by
  let H := PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)
  change closure (H ⁻¹' pi univ (fun i : Fin 2 => Ioo (0 : ℝ) (![curvePeriod, 1] i))) = _
  rw [← H.preimage_closure, closure_pi_set]
  have hclosure (i : Fin 2) : closure (Ioo (0 : ℝ) (![curvePeriod, 1] i)) =
      Icc (0 : ℝ) (![curvePeriod, 1] i) := by
    apply closure_Ioo
    fin_cases i
    · change 0 ≠ curvePeriod
      exact ne_of_lt (by unfold curvePeriod; positivity)
    · norm_num
  simp_rw [hclosure]
  ext p
  simp only [mem_preimage, Set.mem_pi, mem_univ, forall_const, Fin.forall_fin_two, mem_Icc,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change ((0 ≤ p 0 ∧ p 0 ≤ curvePeriod) ∧ (0 ≤ p 1 ∧ p 1 ≤ 1)) ↔
    (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1)
  tauto

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_conformal_on_domain_of_ae
    (A : M64Annulus g c0 c1) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hpoint := m64Annulus_conformal_on_interior_of_ae A
    (hf.mono (hsub.trans hdom)) hconformal
  have hcont (i j : Fin 2) :
      ContinuousOn (fun p => m60AreaGram g A.map p i j) m64AnnulusDomain := by
    intro p hp
    exact (m64AreaGram_entry_contDiffAt
      (hf.contMDiffAt (hO.mem_nhds (hdom hp))) i j).continuousAt.continuousWithinAt
  have hclosure : m64AnnulusDomain ⊆ closure m64AnnulusInterior := by
    rw [m64AnnulusInterior_closure]
  have hdiag : EqOn (fun p => m60AreaGram g A.map p 0 0)
      (fun p => m60AreaGram g A.map p 1 1) m64AnnulusInterior := fun p hp => (hpoint p hp).1
  have hcross : EqOn (fun p => m60AreaGram g A.map p 0 1)
      (fun _ => (0 : ℝ)) m64AnnulusInterior := fun p hp => (hpoint p hp).2
  exact fun p hp => ⟨hdiag.of_subset_closure (hcont 0 0) (hcont 1 1) hsub hclosure hp,
    hcross.of_subset_closure (hcont 0 1) continuousOn_const hsub hclosure hp⟩

theorem m64Annulus_conformal_fderiv_on_domain_of_ae
    (A : M64Annulus g c0 c1) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusDomain,
      fderiv ℝ (fun q => m60AreaGram g A.map q 0 0) p =
          fderiv ℝ (fun q => m60AreaGram g A.map q 1 1) p ∧
        fderiv ℝ (fun q => m60AreaGram g A.map q 0 1) p = 0 := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hpoint := m64Annulus_conformal_on_interior_of_ae A
    (hf.mono (hsub.trans hdom)) hconformal
  have hcont (i j : Fin 2) : ContinuousOn
      (fun p => fderiv ℝ (fun q => m60AreaGram g A.map q i j) p) m64AnnulusDomain := by
    have hGram : ContDiffOn ℝ ∞ (fun q => m60AreaGram g A.map q i j) O :=
      fun p hp => (m64AreaGram_entry_contDiffAt
        (hf.contMDiffAt (hO.mem_nhds hp)) i j).contDiffWithinAt
    exact (hGram.fderiv_of_isOpen hO (m := ∞) (by simp)).continuousOn.mono hdom
  have hdiag : EqOn
      (fun p => fderiv ℝ (fun q => m60AreaGram g A.map q 0 0) p)
      (fun p => fderiv ℝ (fun q => m60AreaGram g A.map q 1 1) p) m64AnnulusInterior := by
    intro p hp
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hp] with q hq
    exact (hpoint q hq).1
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
  exact fun p hp => ⟨hdiag.of_subset_closure (hcont 0 0) (hcont 1 1) hsub hclosure hp,
    hcross.of_subset_closure (hcont 0 1) continuousOn_const hsub hclosure hp⟩

end PoincareConjecture
