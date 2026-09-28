import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConformalInverseRemoval
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateLocalInjective













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)






theorem scalarPotential_gradient_ne_zero_of_local_conjugate_injective
    {H W : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hWs : ContDiff ℝ ∞ W) {U : Set Plane} (hUo : IsOpen U)
    (hUAnn : U ⊆ scalarAnnulus)
    (hform : ∀ x ∈ U, HasFDerivAt W (scalarConjugateForm D H x) x)
    (hinj : InjOn (scalarConjugatePair H W) U) {p : Plane} (hp : p ∈ U) :
    D.gradient H p ≠ 0 := by
  obtain ⟨e, a, lambda, ha, hap, he, -, -, hlambda, hmetric⟩ :=
    exists_local_annular_isothermal_chart g p
  let C := Complex.orthonormalBasisOneI.repr
  let q : OpenPartialHomeomorph ℂ Plane := C.toHomeomorph.toOpenPartialHomeomorph.trans e
  let z : ℂ := C.symm a
  let F : ℂ → ℂ := C.symm ∘ scalarConjugatePair H W ∘ q
  let S : Set ℂ := q.source ∩ q ⁻¹' U
  have hzq : z ∈ q.source := by
    refine ⟨mem_univ _, ?_⟩
    change C (C.symm a) ∈ e.source
    rwa [C.apply_symm_apply]
  have hqz : q z = p := by
    change e (C (C.symm a)) = p
    rw [C.apply_symm_apply, hap]
  have hzS : z ∈ S := ⟨hzq, by change q z ∈ U; rwa [hqz]⟩
  have hSo : IsOpen S := q.isOpen_inter_preimage hUo
  have hqt : Tendsto q (𝓝 z) (𝓝 p) := hqz ▸ (q.continuousAt hzq).tendsto
  have hqS (y : ℂ) (hy : y ∈ S) : ContDiffAt ℝ ∞ (q : ℂ → Plane) y :=
    ((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
      (e.open_source.mem_nhds hy.1.2)).comp y C.contDiff.contDiffAt
  have hpairS (x : Plane) (hx : x ∈ U) : ContDiffAt ℝ ∞ (scalarConjugatePair H W) x :=
    (((contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
      (scalarAnnulus_isOpen.mem_nhds (hUAnn hx))).smul contDiffAt_const).add
        (hWs.contDiffAt.smul contDiffAt_const)
  have hFS (y : ℂ) (hy : y ∈ S) : ContDiffAt ℝ ∞ F y :=
    C.symm.contDiff.contDiffAt.comp y ((hpairS _ hy.2).comp y (hqS y hy))
  have hFi : InjOn F S := by
    intro x hx y hy hxy
    apply q.injOn hx.1 hy.1
    exact hinj hx.2 hy.2 (C.symm.injective hxy)
  have hFo (y : ℂ) (hy : y ∈ S) : 𝓝 (F y) ≤ map F (𝓝 y) := by
    have h := scalarConjugatePair_nhds_le_map D hHc hHs hlap hinner houter hWs (hUAnn hy.2)
      (eventually_of_mem (hUo.mem_nhds hy.2) fun x hx => hform x hx)
    have hm := Filter.map_mono (m := C.symm) h
    have hCn : map C.symm (𝓝 (scalarConjugatePair H W (q y))) =
        𝓝 (C.symm (scalarConjugatePair H W (q y))) :=
      C.symm.toHomeomorph.map_nhds_eq _
    rw [hCn, ← q.map_nhds_eq hy.1, map_map, map_map] at hm
    exact hm
  have hi := scalarPotential_critical_isolated D hHc hHs hlap hinner houter (hUAnn hp)
  rw [eventually_nhdsWithin_iff] at hi
  have hFp : ∀ᶠ y in 𝓝[≠] z,
      ContDiffAt ℝ ∞ F y ∧ IsConformalMap (fderiv ℝ F y) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hSo.mem_nhds hzS, hqt.eventually hi] with y hy hycrit hyz
    have hneq : q y ≠ p := fun heq => hyz (q.injOn hy.1 hzq (heq.trans hqz.symm))
    have hgrad : D.gradient H (q y) ≠ 0 := by
      intro hzero
      apply hycrit hneq
      ext v
      have h := D.inner_gradient H (q y) v
      rw [hzero, map_zero, zero_apply] at h
      simpa only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
        ContinuousLinearMap.comp_apply, zero_apply] using! h.symm
    refine ⟨hFS y hy, ?_⟩
    have hHS := (contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
      (scalarAnnulus_isOpen.mem_nhds (hUAnn hy.2))
    have hpairD : HasFDerivAt (scalarConjugatePair H W)
        (scalarConjugateLinear D H (q y)) (q y) :=
      ((hHS.differentiableAt (by simp)).hasFDerivAt.smul_const _).add
        ((hform _ hy.2).smul_const _)
    have heS := (contMDiffOn_iff_contDiffOn.mp he).contDiffAt
      (e.open_source.mem_nhds hy.1.2)
    have hqD := (heS.differentiableAt (by simp)).hasFDerivAt.comp y C.hasFDerivAt
    have hFD := C.symm.hasFDerivAt.comp y (hpairD.comp y hqD)
    change HasFDerivAt F _ y at hFD
    apply (isConformalMap_iff _).mpr
    refine ⟨g.inner (q y) (D.gradient H (q y)) (D.gradient H (q y)) * lambda (C y),
      mul_pos (g.pos _ _ hgrad) (hlambda _ hy.1.2), ?_⟩
    intro v w
    rw [hFD.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, LinearIsometryEquiv.inner_map_map]
    rw [scalarConjugateLinear_inner]
    have hm := hmetric (C y) hy.1.2 (C v) (C w)
    simp only [RiemannianMetric.pullbackCoefficients, mfderiv_eq_fderiv,
      ContinuousLinearMap.bilinearComp_apply] at hm
    erw [hm, C.inner_map_map]
    ring
  have hFDinj := scalar_locally_injective_regular_of_conformal_punctured hSo
    (fun y hy => (hFS y hy).continuousAt.continuousWithinAt) hFi hFo hzS (hFS z hzS) hFp
  intro hzero
  have hL : scalarConjugateLinear D H p = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change scalarConjugateLinear D H p v = 0
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [scalarConjugateLinear_inner, hzero, map_zero, zero_mul]
  have hHS := (contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
    (scalarAnnulus_isOpen.mem_nhds (hUAnn hp))
  have hpairD : HasFDerivAt (scalarConjugatePair H W) (scalarConjugateLinear D H p) p :=
    ((hHS.differentiableAt (by simp)).hasFDerivAt.smul_const _).add
      ((hform p hp).smul_const _)
  have hFD := C.symm.hasFDerivAt.comp z
    ((hqz.symm ▸ hpairD).comp z ((hqS z hzS).differentiableAt (by simp)).hasFDerivAt)
  change HasFDerivAt F _ z at hFD
  have hDzero : fderiv ℝ F z = 0 := by
    rw [hFD.fderiv]
    simp only [hqz, hL, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  rw [hDzero] at hFDinj
  have h01 : (0 : ℂ) = 1 := hFDinj rfl
  exact zero_ne_one h01

end PoincareConjecture.M64Uniformization
