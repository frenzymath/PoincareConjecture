import PoincareConjecture.Proofs.M60.Mathlib.HarmonicBranchIsolation
import PoincareConjecture.Proofs.M60.Mathlib.ConformalPlaneLaplacian
import PoincareConjecture.Proofs.M60.Mathlib.LocallyIsolatedZeroSet
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUConformality
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUHarmonicEnergyGap
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.Stationarity
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

noncomputable section

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation M60

theorem m60Sphere_chartInverse_contMDiff (p : UnitTwoSphere) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (chartAt LoopPlane p).symm := by
  have ht : (chartAt LoopPlane p).target = univ := by
    let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
    change (stereographic' 2 (-p)).target = univ
    simp
  exact contMDiffOn_univ.mp (ht ▸ contMDiffOn_chart_symm (I := 𝓡 2))

theorem m60SphereChart_transition_data (p : UnitTwoSphere) (z : LoopPlane)
    (hz : (chartAt LoopPlane p).symm z ∈ m60SphereChart.source) :
    let t := m60SphereChart ∘ (chartAt LoopPlane p).symm
    ContDiffAt ℝ ∞ t z ∧ (fderiv ℝ t z).IsInvertible ∧
      ∃ a : ℝ, 0 < a ∧ ∀ v w : LoopPlane,
        inner ℝ (fderiv ℝ t z v) (fderiv ℝ t z w) = a * inner ℝ v w := by
  let c := chartAt LoopPlane p
  let t := m60SphereChart ∘ c.symm
  have htarg : c.target = univ := by
    let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
    change (stereographic' 2 (-p)).target = univ
    simp
  have hc : c.symm.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
  have hs : m60SphereChart.MDifferentiable (𝓡 2) (𝓡 2) := by
    rw [m60SphereChart_eq_chartAt]
    exact ⟨(contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp)⟩
  have hcz : z ∈ c.symm.source := by simpa only [c.symm_source, htarg] using mem_univ z
  have hcsm := m60Sphere_chartInverse_contMDiff p
  have hssm : ContMDiffAt (𝓡 2) (𝓡 2) ∞ m60SphereChart (c.symm z) := by
    rw [m60SphereChart_eq_chartAt] at hz ⊢
    exact (contMDiffOn_chart (I := 𝓡 2) (n := ∞)).contMDiffAt
      ((chartAt LoopPlane (-m60SpherePole)).open_source.mem_nhds hz)
  have htsm : ContDiffAt ℝ ∞ t z :=
    contMDiffAt_iff_contDiffAt.mp (hssm.comp z (hcsm z))
  refine ⟨htsm, ?_, ?_⟩
  · change (fderiv ℝ (m60SphereChart ∘ c.symm) z).IsInvertible
    rw [← mfderiv_eq_fderiv, mfderiv_comp z
      (hssm.mdifferentiableAt (by simp)) ((hcsm z).mdifferentiableAt (by simp))]
    exact (show (mfderiv (𝓡 2) (𝓡 2) m60SphereChart (c.symm z)).IsInvertible from
      ⟨hs.mfderiv hz, rfl⟩).comp ⟨hc.mfderiv hcz, rfl⟩
  · let a : ℝ := (16 / (‖z‖ ^ 2 + 4) ^ 2) / (16 / (‖t z‖ ^ 2 + 4) ^ 2)
    have ha : 0 < a := by dsimp only [a]; positivity
    refine ⟨a, ha, ?_⟩
    intro v w
    have he : (m60SphereParameter ∘ t) =ᶠ[𝓝 z] c.symm := by
      filter_upwards [hcsm.continuous.continuousAt.preimage_mem_nhds
        (m60SphereChart.open_source.mem_nhds hz)] with y hy
      exact m60SphereChart.left_inv hy
    have hi : ContDiffAt ℝ ∞ (fun q => (m60SphereParameter q).1) (t z) := by
      let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
      exact contMDiffAt_iff_contDiffAt.mp
        ((contMDiff_coe_sphere (E := LoopAmbient) (n := 2) (m := ∞)
          (m60SphereParameter (t z))).comp _ (m60SphereParameter_contMDiff (t z)))
    have he' : (fun q => (m60SphereParameter (t q)).1) =ᶠ[𝓝 z]
        (fun q => (c.symm q).1) := he.mono fun _ h => congrArg Subtype.val h
    have hderiv (v : LoopPlane) :
        fderiv ℝ (fun q => (m60SphereParameter q).1) (t z) (fderiv ℝ t z v) =
          fderiv ℝ (fun q => (c.symm q).1) z v := by
      have h := he'.fderiv_eq (𝕜 := ℝ)
      change fderiv ℝ ((fun q => (m60SphereParameter q).1) ∘ t) z = _ at h
      rw [fderiv_comp z (hi.differentiableAt (by simp))
        (htsm.differentiableAt (by simp))] at h
      exact congrArg (fun L => L v) h
    have h : inner ℝ
        (fderiv ℝ (fun q => (m60SphereParameter q).1) (t z) (fderiv ℝ t z v))
        (fderiv ℝ (fun q => (m60SphereParameter q).1) (t z) (fderiv ℝ t z w)) =
        (16 / (‖t z‖ ^ 2 + 4) ^ 2) * inner ℝ (fderiv ℝ t z v) (fderiv ℝ t z w) := by
      simpa only [m60SphereParameter, m60SphereChart_eq_chartAt] using
        M36.sphere_chart_inverse_fderiv_inner (-m60SpherePole) (t z)
          (fderiv ℝ t z v) (fderiv ℝ t z w)
    rw [hderiv v, hderiv w, M36.sphere_chart_inverse_fderiv_inner] at h
    have hσ : (16 / (‖t z‖ ^ 2 + 4) ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    change inner ℝ (fderiv ℝ t z v) (fderiv ℝ t z w) = a * inner ℝ v w
    dsimp only [a]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hσ).2
    exact (mul_comm _ _).trans h.symm

private noncomputable def chartTension {n : ℕ}
    (Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane) :
    EuclideanSpace ℝ (Fin n) :=
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  fderiv ℝ (fderiv ℝ u) z (e 0) (e 0) + fderiv ℝ (fderiv ℝ u) z (e 1) (e 1) +
    Γ (u z) (fderiv ℝ u z (e 0)) (fderiv ℝ u z (e 0)) +
    Γ (u z) (fderiv ℝ u z (e 1)) (fderiv ℝ u z (e 1))

private theorem chartTension_congr {n : ℕ}
    (Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n))
    {u v : LoopPlane → EuclideanSpace ℝ (Fin n)} {z : LoopPlane} (h : u =ᶠ[𝓝 z] v) :
    chartTension Γ u z = chartTension Γ v z := by
  simp only [chartTension, h.eq_of_nhds, h.fderiv_eq, h.fderiv.fderiv_eq]

private theorem chartTension_continuousAt {n : ℕ}
    {Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {z : LoopPlane}
    (hu : ContDiffAt ℝ ∞ u z) (hΓ : ContDiffAt ℝ ∞ Γ (u z)) :
    ContinuousAt (chartTension Γ u) z := by
  have hd := hu.fderiv_right (m := ∞) (by simp)
  have hdd := hd.fderiv_right (m := ∞) (by simp)
  have hcol (i : Fin 2) := hd.clm_apply
    (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 2) ℝ i))
  have hdiag (i : Fin 2) := (hdd.clm_apply
    (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 2) ℝ i))).clm_apply
      (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 2) ℝ i))
  exact (((hdiag 0).add (hdiag 1)).add
    (((hΓ.comp z hu).clm_apply (hcol 0)).clm_apply (hcol 0))).add
      (((hΓ.comp z hu).clm_apply (hcol 1)).clm_apply (hcol 1)) |>.continuousAt

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereChartHarmonic_in_atlas (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (p : UnitTwoSphere) (b : M) (z : LoopPlane)
    (hz : f ((chartAt LoopPlane p).symm z) ∈ (extChartAt (𝓡 n) b).source) :
    let u := (extChartAt (𝓡 n) b) ∘ (f ∘ (chartAt LoopPlane p).symm)
    let Γ := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
    chartTension Γ u z = 0 := by
  let c := extChartAt (𝓡 n) b
  let ψ := (chartAt LoopPlane p).symm
  let u := c ∘ (f ∘ ψ)
  let Γ := christoffelBilinear (g.pullbackCoefficients c.symm)
  let O := (f ∘ ψ) ⁻¹' c.source
  have hψ := m60Sphere_chartInverse_contMDiff p
  have hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ (f ∘ ψ) := hf.comp hψ
  have hO : IsOpen O := hφ.continuous.isOpen_preimage _ (isOpen_extChartAt_source b)
  have hu (w : LoopPlane) (hw : w ∈ O) : ContDiffAt ℝ ∞ u w :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (x := b) (n := ∞)
        (by simpa only [O, c, mem_preimage, Function.comp_apply, extChartAt_source]
          using hw)).comp w (hφ w))
  have hΓ (w : LoopPlane) (hw : w ∈ O) : ContDiffAt ℝ ∞ Γ (u w) :=
    contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients b).contDiffAt
        ((isOpen_extChartAt_target b).mem_nhds (c.map_source hw)))
      (g.isInvertible_chartCoefficients b (c.map_source hw))
  have hoff (w : LoopPlane) (hw : w ∈ O) (hwp : ψ w ∈ m60SphereChart.source) :
      chartTension Γ u w = 0 := by
    let t := m60SphereChart ∘ ψ
    let v := c ∘ (f ∘ m60SphereParameter)
    have he : (v ∘ t) =ᶠ[𝓝 w] u := by
      filter_upwards [hψ.continuous.continuousAt.preimage_mem_nhds
        (m60SphereChart.open_source.mem_nhds hwp)] with q hq
      exact congrArg (fun x => c (f x)) (m60SphereChart.left_inv hq)
    have hwpt : m60SphereParameter (t w) = ψ w := m60SphereChart.left_inv hwp
    have hw' : f (m60SphereParameter (t w)) ∈ c.source := by rw [hwpt]; exact hw
    have hv : ContDiffAt ℝ ∞ v (t w) := contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (x := b) (n := ∞)
        (by simpa only [c, extChartAt_source, Function.comp_apply] using hw')).comp _
          ((hf.comp m60SphereParameter_contMDiff) (t w)))
    obtain ⟨ht, htinv, a, ha, hgram⟩ := m60SphereChart_transition_data p w hwp
    have ht2 : ContDiffAt ℝ 2 t w := ht.of_le (WithTop.coe_le_coe.mpr le_top)
    have hv2 : ContDiffAt ℝ 2 v (t w) := hv.of_le (WithTop.coe_le_coe.mpr le_top)
    have hsurj : Function.Surjective (fderiv ℝ t w) := by
      obtain ⟨L, hL⟩ := htinv
      rw [← hL]
      exact L.surjective
    have hlocal := hψ.continuous.continuousAt.preimage_mem_nhds
      (m60SphereChart.open_source.mem_nhds hwp)
    have hself : (fun q => inner ℝ (fderiv ℝ t q (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (fderiv ℝ t q (EuclideanSpace.basisFun (Fin 2) ℝ 0))) =ᶠ[𝓝 w]
        (fun q => inner ℝ (fderiv ℝ t q (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (fderiv ℝ t q (EuclideanSpace.basisFun (Fin 2) ℝ 1))) := by
      filter_upwards [hlocal] with q hq
      obtain ⟨_, _, a, _, hg⟩ := m60SphereChart_transition_data p q hq
      rw [hg, hg]
      simp
    have horth : (fun q => inner ℝ (fderiv ℝ t q (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (fderiv ℝ t q (EuclideanSpace.basisFun (Fin 2) ℝ 1))) =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hlocal] with q hq
      obtain ⟨_, _, a, _, hg⟩ := m60SphereChart_transition_data p q hq
      rw [hg]
      simp [EuclideanSpace.inner_single_left, EuclideanSpace.basisFun]
    have hlap := laplacian_eq_zero_of_conformal_plane ht2 hsurj hself horth
    have hτ : chartTension Γ v (t w) = 0 := by
      have h := hharm b (t w) hw'
      change covDerivAlong Γ v
        (fun r => fderiv ℝ v r (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) (t w) + covDerivAlong Γ v
        (fun r => fderiv ℝ v r (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) (t w) = 0 at h
      simp only [covDerivAlong, fderiv_column hv2] at h
      unfold chartTension
      convert h using 1
      abel
    rw [← chartTension_congr Γ he]
    exact covariant_laplacian_comp_eq_zero Γ hv2 ht2 ha
      (fun i j => by
        simpa [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left] using
          (hgram (EuclideanSpace.basisFun (Fin 2) ℝ i)
          (EuclideanSpace.basisFun (Fin 2) ℝ j))) hlap hτ
  by_cases hzp : ψ z ∈ m60SphereChart.source
  · exact hoff z hz hzp
  · have hpole : ψ z = m60SpherePole := by simpa [m60SphereChart] using hzp
    have htarget : (chartAt LoopPlane p).target = univ := by
      let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
      change (stereographic' 2 (-p)).target = univ
      simp
    have hψinj : Function.Injective ψ := by
      intro x y h
      exact (chartAt LoopPlane p).symm.injOn
        (by simpa only [OpenPartialHomeomorph.symm_source, htarget] using mem_univ x)
        (by simpa only [OpenPartialHomeomorph.symm_source, htarget] using mem_univ y) h
    have he : chartTension Γ u =ᶠ[𝓝[≠] z] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hO.mem_nhds hz)]
        with w hw hwO
      apply hoff w hwO
      have hne : ψ w ≠ m60SpherePole := fun h => hw (hψinj (h.trans hpole.symm))
      simpa [m60SphereChart] using hne
    exact tendsto_nhds_unique
      ((chartTension_continuousAt (hu z hz) (hΓ z hz)).tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' he.symm)

private theorem plane_differential_zero_alternative
    {Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {O : Set LoopPlane}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 2 u O)
    (hΓ : ∀ z ∈ O, ContDiffAt ℝ 1 Γ (u z))
    (hsym : ∀ z ∈ O, ∀ a b, Γ (u z) a b = Γ (u z) b a)
    (hτ : ∀ z ∈ O, chartTension Γ u z = 0) {z : LoopPlane} (hz : z ∈ O) :
    (∀ᶠ w in 𝓝 z, fderiv ℝ u w = 0) ∨ ∀ᶠ w in 𝓝[≠] z, fderiv ℝ u w ≠ 0 := by
  let C := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let L := C.toContinuousLinearMap
  let v := u ∘ L
  let V := L ⁻¹' O
  have hL1 : L 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [L, C, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]
  have hLI : L Complex.I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [L, C, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]
  have hV : IsOpen V := L.continuous.isOpen_preimage _ hO
  have huAt (w : ℂ) (hw : w ∈ V) := hu.contDiffAt (hO.mem_nhds hw)
  have hL2 (w : ℂ) : ContDiffAt ℝ 2 L w := L.contDiff.contDiffAt
  have hvAt (w : ℂ) (hw : w ∈ V) : ContDiffAt ℝ 2 v w :=
    (huAt w hw).comp w (hL2 w)
  have hD (w : ℂ) (hw : w ∈ V) : fderiv ℝ v w = (fderiv ℝ u (L w)).comp L := by
    rw [fderiv_comp w ((huAt w hw).differentiableAt (by simp)) L.differentiableAt,
      L.fderiv]
  have hDD (w : ℂ) (hw : w ∈ V) (d : ℂ) :
      fderiv ℝ (fderiv ℝ v) w d d = fderiv ℝ (fderiv ℝ u) (L w) (L d) (L d) := by
    rw [second_fderiv_comp (huAt w hw) (hL2 w)]
    have heqL : fderiv ℝ (L : ℂ → LoopPlane) = fun _ => L := by
      funext w
      exact L.fderiv
    simp only [heqL, fderiv_const_apply, zero_apply, map_zero, add_zero]
  have hvτ (w : ℂ) (hw : w ∈ V) :
      covDerivAlong Γ v (fun q => fderiv ℝ v q 1) 1 w +
        covDerivAlong Γ v (fun q => fderiv ℝ v q Complex.I) Complex.I w = 0 := by
    simp only [covDerivAlong, fderiv_column (hvAt w hw), hDD w hw,
      hD w hw, ContinuousLinearMap.comp_apply, hL1, hLI]
    have h := hτ (L w) hw
    unfold chartTension at h
    change _ + _ + _ + _ = 0 at h
    dsimp only [v, Function.comp_apply]
    convert h using 1
    abel
  have hzV : C.symm z ∈ V := by simpa only [V, mem_preimage, L,
    ContinuousLinearEquiv.coe_coe, C.apply_symm_apply] using hz
  have ha := harmonic_differential_eventually_zero_or_isolated hV
    (fun w hw => (hvAt w hw).contDiffWithinAt)
    (fun w hw => hΓ (L w) hw) (fun w hw => hsym (L w) hw) hvτ hzV
  have hzero (w : ℂ) (hw : w ∈ V) : fderiv ℝ v w = 0 ↔ fderiv ℝ u (L w) = 0 := by
    rw [hD w hw]
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro y
      obtain ⟨x, hx⟩ := C.surjective y
      have he := congrArg (fun D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin n) => D x) h
      change fderiv ℝ u (L w) (C x) = 0 at he
      simpa only [hx, zero_apply] using he
    · intro h
      rw [h, ContinuousLinearMap.zero_comp]
  have hzero' (w : LoopPlane) (hw : w ∈ O) :
      fderiv ℝ v (C.symm w) = 0 ↔ fderiv ℝ u w = 0 := by
    have hwV : C.symm w ∈ V := by simpa only [V, mem_preimage, L,
      ContinuousLinearEquiv.coe_coe, C.apply_symm_apply] using hw
    simpa only [L, ContinuousLinearEquiv.coe_coe, C.apply_symm_apply] using hzero _ hwV
  rcases ha with ha | ha
  · left
    filter_upwards [C.symm.continuous.continuousAt.eventually ha, hO.mem_nhds hz] with w hw hwO
    exact (hzero' w hwO).mp hw
  · right
    rw [eventually_nhdsWithin_iff] at ha ⊢
    filter_upwards [C.symm.continuous.continuousAt.eventually ha, hO.mem_nhds hz] with w hw hwO
    intro hwz hzero
    exact hw (fun h => hwz (C.symm.injective h)) ((hzero' w hwO).mpr hzero)

private theorem chart_differential_eq_zero_iff
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (p : UnitTwoSphere) (b : M) (z : LoopPlane)
    (hz : f ((chartAt LoopPlane p).symm z) ∈ (extChartAt (𝓡 n) b).source) :
    fderiv ℝ ((extChartAt (𝓡 n) b) ∘ (f ∘ (chartAt LoopPlane p).symm)) z = 0 ↔
      mfderiv (𝓡 2) (𝓡 n) f ((chartAt LoopPlane p).symm z) = 0 := by
  let c := extChartAt (𝓡 n) b
  let ψ := (chartAt LoopPlane p).symm
  have hψ := m60Sphere_chartInverse_contMDiff p
  have hcd : MDifferentiableAt (𝓡 n) (𝓡 n) c (f (ψ z)) :=
    (contMDiffAt_extChartAt' (x := b) (n := ∞)
      (by simpa only [extChartAt_source] using hz)).mdifferentiableAt (by simp)
  have hA := isInvertible_mfderiv_extChartAt (I := 𝓡 n) hz
  have hB : (mfderiv (𝓡 2) (𝓡 2) ψ z).IsInvertible := by
    have hψd : ψ.MDifferentiable (𝓡 2) (𝓡 2) :=
      ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
        (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
    have hzs : z ∈ ψ.source := by
      let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
      change z ∈ (stereographic' 2 (-p)).target
      simp
    exact ⟨hψd.mfderiv hzs, rfl⟩
  rw [← mfderiv_eq_fderiv, mfderiv_comp z hcd
    ((hf.comp hψ).mdifferentiable (by simp) z), mfderiv_comp z
      (hf.mdifferentiable (by simp) _) (hψ.mdifferentiable (by simp) z)]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    have he := congrArg (fun D => D ((mfderiv (𝓡 2) (𝓡 2) ψ z).inverse v)) h
    change mfderiv (𝓡 n) (𝓡 n) c (f (ψ z))
      (mfderiv (𝓡 2) (𝓡 n) f (ψ z) (mfderiv (𝓡 2) (𝓡 2) ψ z
        ((mfderiv (𝓡 2) (𝓡 2) ψ z).inverse v))) = 0 at he
    rw [hB.self_apply_inverse] at he
    change mfderiv (𝓡 2) (𝓡 n) f (ψ z) v = 0
    exact hA.injective (he.trans (map_zero (mfderiv (𝓡 n) (𝓡 n) c (f (ψ z)))).symm)
  · intro h
    rw [h, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

theorem m60SphereBranchSet_local_alternative (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (p : UnitTwoSphere) :
    m60SphereBranchSet (n := n) f ∈ 𝓝 p ∨
      ∀ᶠ q in 𝓝[≠] p, q ∉ m60SphereBranchSet (n := n) f := by
  let c := chartAt LoopPlane p
  let b := f p
  let d := extChartAt (𝓡 n) b
  let u := d ∘ (f ∘ c.symm)
  let Γ := christoffelBilinear (g.pullbackCoefficients d.symm)
  let O := (f ∘ c.symm) ⁻¹' d.source
  have hψ := m60Sphere_chartInverse_contMDiff p
  have hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ (f ∘ c.symm) := hf.comp hψ
  have hO : IsOpen O := hφ.continuous.isOpen_preimage _ (isOpen_extChartAt_source b)
  have hu (w : LoopPlane) (hw : w ∈ O) : ContDiffAt ℝ ∞ u w :=
    contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' (x := b) (n := ∞)
      (by simpa only [O, d, mem_preimage, Function.comp_apply, extChartAt_source]
        using hw)).comp w (hφ w))
  have hΓ (w : LoopPlane) (hw : w ∈ O) : ContDiffAt ℝ ∞ Γ (u w) :=
    contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients b).contDiffAt
        ((isOpen_extChartAt_target b).mem_nhds (d.map_source hw)))
      (g.isInvertible_chartCoefficients b (d.map_source hw))
  have hcp : p ∈ c.source := mem_chart_source _ _
  have hzp : c.symm (c p) = p := c.left_inv hcp
  have hzO : c p ∈ O := by
    change f (c.symm (c p)) ∈ d.source
    rw [hzp]
    exact mem_extChartAt_source _
  have ha := plane_differential_zero_alternative hO
    (fun w hw => ((hu w hw).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt)
    (fun w hw => (hΓ w hw).of_le (by simp))
    (fun w _ => christoffelBilinear_chart_symm g b (u w))
    (fun w hw => m60SphereChartHarmonic_in_atlas g f hf hharm p b w hw) hzO
  have hloc : ∀ᶠ q in 𝓝 p, q ∈ c.source ∧ f q ∈ d.source := by
    filter_upwards [c.open_source.mem_nhds hcp,
      hf.continuous.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source b).mem_nhds (mem_extChartAt_source (I := 𝓡 n) (f p)))]
      with q hq hqf
    exact ⟨hq, hqf⟩
  have hziff (q : UnitTwoSphere) (hq : q ∈ c.source) (hqf : f q ∈ d.source) :
      fderiv ℝ u (c q) = 0 ↔ q ∈ m60SphereBranchSet (n := n) f := by
    have hqz : c.symm (c q) = q := c.left_inv hq
    have hq' : f (c.symm (c q)) ∈ d.source := by rw [hqz]; exact hqf
    have h := chart_differential_eq_zero_iff f hf p b (c q) hq'
    change fderiv ℝ u (c q) = 0 ↔ mfderiv (𝓡 2) (𝓡 n) f (c.symm (c q)) = 0 at h
    rw [hqz] at h
    exact h
  have hcc : ContinuousAt c p := c.continuousAt hcp
  rcases ha with ha | ha
  · left
    filter_upwards [hcc.eventually ha, hloc] with q hq hqO
    exact (hziff q hqO.1 hqO.2).mp hq
  · right
    rw [eventually_nhdsWithin_iff] at ha ⊢
    filter_upwards [hcc.eventually ha, hloc] with q hq hqO
    intro hqp hqS
    exact hq (fun h => hqp (c.injOn hqO.1 hcp h)) ((hziff q hqO.1 hqO.2).mpr hqS)

variable [T2Space M]

theorem m60SphereBranchSet_finite_of_chartHarmonic (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (hnonconst : ∃ p q, f p ≠ f q) :
    (m60SphereBranchSet (n := n) f).Finite := by
  let : PreconnectedSpace UnitTwoSphere := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num [LoopAmbient]) (0 : LoopAmbient) 1)
  apply finite_of_locally_mem_or_isolated _ (m60SphereBranchSet_local_alternative g f hf hharm)
  intro hfull
  have hd (p : UnitTwoSphere) : mfderiv (𝓡 2) (𝓡 n) f p = 0 := by
    exact (show p ∈ m60SphereBranchSet (n := n) f from hfull ▸ mem_univ p)
  have he (z : LoopPlane) : m60SphereEnergyDensity g f z = 0 := by
    unfold m60SphereEnergyDensity m60EnergyDensity m60AreaGram
    rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _), hd]
    rw [Matrix.trace_fin_two]
    simp only [ContinuousLinearMap.zero_comp, zero_apply, map_zero, zero_add, mul_zero]
  obtain ⟨c, hc⟩ := m60Sphere_constant_of_energyDensity_zero g f (hf.of_le (by simp)) he
  obtain ⟨p, q, hpq⟩ := hnonconst
  exact hpq ((hc p).trans (hc q).symm)

omit [T2Space M] in

theorem m60WeaklyConformal_injective_off_branchSet (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hc : M60WeaklyConformal g f) (p : UnitTwoSphere)
    (hp : p ∉ m60SphereBranchSet (n := n) f) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 n) f p) := by
  let : NormedAddCommGroup (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (NormedAddCommGroup LoopPlane)
  let : InnerProductSpace ℝ (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (InnerProductSpace ℝ LoopPlane)
  obtain ⟨s, _, hpair⟩ := hc p
  have hs : s ≠ 0 := by
    intro hs
    apply hp
    change mfderiv (𝓡 2) (𝓡 n) f p = 0
    apply ContinuousLinearMap.ext
    intro v
    change mfderiv (𝓡 2) (𝓡 n) f p v = 0
    by_contra hv
    have hpos := g.pos (f p) _ hv
    rw [hpair, hs, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have hzero (v : TangentSpace (𝓡 2) p) (hv : mfderiv (𝓡 2) (𝓡 n) f p v = 0) : v = 0 := by
    have h := hpair v v
    simp only [hv, map_zero] at h
    have hr := (mul_eq_zero.mp h.symm).resolve_left hs
    rw [m60RoundSphereInner_eq_inner] at hr
    exact inner_self_eq_zero.mp hr
  intro v w hvw
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hvw, sub_self]

theorem m60BranchedMinimalSphere_of_energyStationary (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hnonconst : ∃ p q, f p ≠ f q) (hstat : M60EnergyStationary g f) :
    M60BranchedMinimalSphere g f := by
  have hharm := m60EnergyStationary_chartHarmonic g f hf hstat
  have hc := m60WeaklyConformal_of_chartHarmonic g f hf hharm
  exact ⟨hf, hnonconst, hc, hstat,
    m60SphereBranchSet_finite_of_chartHarmonic g f hf hharm hnonconst,
    m60WeaklyConformal_injective_off_branchSet g f hc⟩

end PoincareConjecture

end
