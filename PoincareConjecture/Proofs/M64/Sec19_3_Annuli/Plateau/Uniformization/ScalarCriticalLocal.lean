import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarComplexHarmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarPotential_local_critical_alternative {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    {p : Plane} (hp : p ∈ scalarAnnulus) :
    (∀ᶠ y in 𝓝 p, fderiv ℝ H y = 0) ∨
      ∀ᶠ y in 𝓝[≠] p, fderiv ℝ H y ≠ 0 := by
  obtain ⟨e, a, lambda, ha, hap, he, hei, -, hlambda, hmetric⟩ :=
    exists_local_annular_isothermal_chart g p
  let L := Complex.orthonormalBasisOneI.repr
  let q : OpenPartialHomeomorph ℂ Plane := L.toHomeomorph.toOpenPartialHomeomorph.trans e
  let z : ℂ := L.symm a
  have hz : z ∈ q.source := by
    refine ⟨mem_univ _, ?_⟩
    change L (L.symm a) ∈ e.source
    rwa [L.apply_symm_apply]
  have hqz : q z = p := by
    change e (L (L.symm a)) = p
    rw [L.apply_symm_apply, hap]
  have hPlane := scalar_harmonic_in_isothermal_chart D e he hei hlambda hmetric
    scalarAnnulus_isOpen hHs hlap a ⟨ha, by change e a ∈ scalarAnnulus; rwa [hap]⟩
  have hComplex : InnerProductSpace.HarmonicAt (H ∘ q) z := by
    have h := scalar_harmonicAt_complex_coordinates (z := z) (u := H ∘ e)
      (by simpa only [z, L, LinearIsometryEquiv.apply_symm_apply] using hPlane)
    exact h
  let S := q.source ∩ q ⁻¹' scalarAnnulus
  have hS : IsOpen S :=
    q.continuousOn.isOpen_inter_preimage q.open_source scalarAnnulus_isOpen
  have hzS : z ∈ S := ⟨hz, by change q z ∈ scalarAnnulus; rwa [hqz]⟩
  have hD : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hzero (y : ℂ) (hy : y ∈ S) :
      fderiv ℝ (H ∘ q) y = 0 ↔ fderiv ℝ H (q y) = 0 := by
    have hys : L y ∈ e.source := hy.1.2
    have heD := (contMDiffOn_iff_contDiffOn.mp he).contDiffAt
      (e.open_source.mem_nhds hys) |>.differentiableAt (by simp)
    have hqD : DifferentiableAt ℝ (q : ℂ → Plane) y := heD.comp y L.differentiableAt
    have hH := (contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
      (scalarAnnulus_isOpen.mem_nhds hy.2) |>.differentiableAt (by simp)
    have hsurj : Function.Surjective (fderiv ℝ q y) := by
      change Function.Surjective (fderiv ℝ ((e : Plane → Plane) ∘ L) y)
      rw [fderiv_comp y heD L.differentiableAt, L.hasFDerivAt.fderiv]
      have hes : Function.Surjective (fderiv ℝ e (L y)) := by
        simpa only [mfderiv_eq_fderiv, TangentSpace] using hD.mfderiv_surjective hys
      exact hes.comp L.surjective
    rw [fderiv_comp y hH hqD]
    constructor
    · intro h
      ext v
      obtain ⟨w, rfl⟩ := hsurj v
      exact congrArg (fun A : ℂ →L[ℝ] ℝ => A w) h
    · intro h
      simp [h]
  rcases scalar_harmonic_differential_alternative hComplex with hzeroLocal | hisolated
  · left
    rw [← hqz, q.eventually_nhds _ hz]
    filter_upwards [hzeroLocal, hS.mem_nhds hzS] with y hy hyS
    exact (hzero y hyS).mp hy
  · right
    have hne : ∀ᶠ y in 𝓝[≠] z, fderiv ℝ H (q y) ≠ 0 := by
      filter_upwards [hisolated, eventually_nhdsWithin_of_eventually_nhds (hS.mem_nhds hzS)]
        with y hy hyS
      exact fun h => hy ((hzero y hyS).mpr h)
    rw [eventually_nhdsWithin_iff] at hne
    rw [← hqz, eventually_nhdsWithin_iff]
    filter_upwards [(q.tendsto_symm hz).eventually hne, q.eventually_right_inverse' hz]
      with y hy hright hneq
    have hsymm : q.symm y ≠ z := by
      intro heq
      exact hneq (hright.symm.trans (congrArg q heq))
    simpa only [hright] using hy hsymm

end PoincareConjecture.M64Uniformization
