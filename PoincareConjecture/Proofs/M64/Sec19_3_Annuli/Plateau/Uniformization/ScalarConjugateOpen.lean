import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateConformal
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarComplexOpen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCriticalDiscrete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def scalarConjugatePair (H V : Plane → ℝ) (x : Plane) : Plane :=
  H x • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
    V x • EuclideanSpace.basisFun (Fin 2) ℝ 1

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarConjugatePair_open_and_discrete {H V : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hVs : ContDiff ℝ ∞ V) {p : Plane} (hp : p ∈ scalarAnnulus)
    (hform : ∀ᶠ x in 𝓝 p, HasFDerivAt V (scalarConjugateForm D H x) x) :
    (𝓝 (scalarConjugatePair H V p) ≤ map (scalarConjugatePair H V) (𝓝 p)) ∧
      ∀ᶠ y in 𝓝[≠] p, scalarConjugatePair H V y ≠ scalarConjugatePair H V p := by
  obtain ⟨e, a, lambda, ha, hap, he, hei, -, hlambda, hmetric⟩ :=
    exists_local_annular_isothermal_chart g p
  let C := Complex.orthonormalBasisOneI.repr
  let q : OpenPartialHomeomorph ℂ Plane := C.toHomeomorph.toOpenPartialHomeomorph.trans e
  let z : ℂ := C.symm a
  let F : ℂ → ℂ := C.symm ∘ scalarConjugatePair H V ∘ q
  have hz : z ∈ q.source := by
    refine ⟨mem_univ _, ?_⟩
    change C (C.symm a) ∈ e.source
    rwa [C.apply_symm_apply]
  have hqz : q z = p := by
    change e (C (C.symm a)) = p
    rw [C.apply_symm_apply, hap]
  have hqt : Tendsto q (𝓝 z) (𝓝 p) := hqz ▸ (q.continuousAt hz).tendsto
  have hFcont : ContinuousAt F z := C.symm.continuousAt.comp
    (((hHc.smul continuous_const).add (hVs.continuous.smul continuous_const)).continuousAt.comp
      (q.continuousAt hz))
  have hi := scalarPotential_critical_isolated D hHc hHs hlap hinner houter hp
  rw [eventually_nhdsWithin_iff] at hi
  have hFconf : ∀ᶠ y in 𝓝[≠] z,
      ContDiffAt ℝ ∞ F y ∧ IsConformalMap (fderiv ℝ F y) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [q.open_source.mem_nhds hz, hqt.eventually
      (scalarAnnulus_isOpen.mem_nhds hp), hqt.eventually hform, hqt.eventually hi]
      with y hy hyA hyV hycrit hyz
    have hneq : q y ≠ p := by
      intro heq
      exact hyz (q.injOn hy hz (heq.trans hqz.symm))
    have hgrad : D.gradient H (q y) ≠ 0 := by
      intro hzero
      apply hycrit hneq
      ext v
      have h := D.inner_gradient H (q y) v
      rw [hzero, map_zero, zero_apply] at h
      simpa only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
        ContinuousLinearMap.comp_apply, zero_apply] using! h.symm
    have heS : ContDiffAt ℝ ∞ (e : Plane → Plane) (C y) :=
      (contMDiffOn_iff_contDiffOn.mp he).contDiffAt (e.open_source.mem_nhds hy.2)
    have hqS : ContDiffAt ℝ ∞ (q : ℂ → Plane) y := heS.comp y C.contDiff.contDiffAt
    have hHS := (contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
      (scalarAnnulus_isOpen.mem_nhds hyA)
    have hpairS : ContDiffAt ℝ ∞ (scalarConjugatePair H V) (q y) :=
      (hHS.smul contDiffAt_const).add (hVs.contDiffAt.smul contDiffAt_const)
    refine ⟨C.symm.contDiff.contDiffAt.comp y (hpairS.comp y hqS), ?_⟩
    have hpairD : HasFDerivAt (scalarConjugatePair H V)
        (scalarConjugateLinear D H (q y)) (q y) :=
      ((hHS.differentiableAt (by simp)).hasFDerivAt.smul_const _).add
        (hyV.smul_const _)
    have hqD := (heS.differentiableAt (by simp)).hasFDerivAt.comp y C.hasFDerivAt
    have hFD := C.symm.hasFDerivAt.comp y (hpairD.comp y hqD)
    change HasFDerivAt F _ y at hFD
    apply (isConformalMap_iff _).mpr
    refine ⟨g.inner (q y) (D.gradient H (q y)) (D.gradient H (q y)) * lambda (C y),
      mul_pos (g.pos _ _ hgrad) (hlambda _ hy.2), ?_⟩
    intro v w
    rw [hFD.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, LinearIsometryEquiv.inner_map_map]
    rw [scalarConjugateLinear_inner]
    have hm := hmetric (C y) hy.2 (C v) (C w)
    simp only [RiemannianMetric.pullbackCoefficients, mfderiv_eq_fderiv,
      ContinuousLinearMap.bilinearComp_apply] at hm
    erw [hm, C.inner_map_map]
    ring
  have hopen := scalar_nhds_le_map_of_conformal_punctured hFcont hFconf
  have hmap := Filter.map_mono (m := C) hopen
  have hnhds : map C (𝓝 (F z)) = 𝓝 (scalarConjugatePair H V (q z)) := by
    calc
      map C (𝓝 (F z)) = 𝓝 (C (F z)) := C.toHomeomorph.map_nhds_eq _
      _ = _ := by simp only [F, Function.comp_apply, C.apply_symm_apply]
  rw [hnhds, map_map] at hmap
  have heq : C ∘ F = scalarConjugatePair H V ∘ q := by
    funext y
    exact C.apply_symm_apply _
  rw [heq, ← map_map, q.map_nhds_eq hz, hqz] at hmap
  refine ⟨hmap, ?_⟩
  have hfi := scalar_fiber_isolated_of_conformal_punctured hFcont hFconf
  rw [eventually_nhdsWithin_iff] at hfi
  rw [← hqz, eventually_nhdsWithin_iff]
  filter_upwards [(q.tendsto_symm hz).eventually hfi, q.eventually_right_inverse' hz]
    with y hy hright hneq
  have hsymm : q.symm y ≠ z := by
    intro heq
    exact hneq (hright.symm.trans (congrArg q heq))
  intro hpair
  apply hy hsymm
  change C.symm (scalarConjugatePair H V (q (q.symm y))) =
    C.symm (scalarConjugatePair H V (q z))
  rw [hright, hpair]

theorem scalarConjugatePair_nhds_le_map {H V : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hVs : ContDiff ℝ ∞ V) {p : Plane} (hp : p ∈ scalarAnnulus)
    (hform : ∀ᶠ x in 𝓝 p, HasFDerivAt V (scalarConjugateForm D H x) x) :
    𝓝 (scalarConjugatePair H V p) ≤ map (scalarConjugatePair H V) (𝓝 p) :=
  (scalarConjugatePair_open_and_discrete D hHc hHs hlap hinner houter hVs hp hform).1

theorem exists_open_local_annular_conjugate {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {p : Plane} (hp : p ∈ scalarAnnulus) :
    ∃ (r : ℝ) (V : Plane → ℝ), 0 < r ∧ Metric.ball p r ⊆ scalarAnnulus ∧
      ContDiff ℝ ∞ V ∧ (∀ x ∈ Metric.ball p r,
        HasFDerivAt V (scalarConjugateForm D H x) x) ∧
      𝓝 (scalarConjugatePair H V p) ≤ map (scalarConjugatePair H V) (𝓝 p) := by
  obtain ⟨r, V, hr, hsub, hVs, hform⟩ := exists_local_annular_conjugate D hHs hlap hp
  exact ⟨r, V, hr, hsub, hVs, hform,
    scalarConjugatePair_nhds_le_map D hHc hHs hlap hinner houter hVs hp
      (eventually_of_mem (Metric.ball_mem_nhds p hr) fun x hx => hform x hx)⟩

end PoincareConjecture.M64Uniformization
