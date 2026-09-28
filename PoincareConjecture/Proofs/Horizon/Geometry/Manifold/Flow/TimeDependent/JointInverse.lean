import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology
namespace Poincare.Manifold
private theorem exists_smooth_euclidean_localInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {f : E → E}
    (hf : ContDiffOn ℝ ∞ f U) {p : E} (hp : p ∈ U)
    (hbij : Function.Bijective (fderiv ℝ f p)) :
    ∃ Q : OpenPartialHomeomorph E E,
      p ∈ Q.source ∧ Q.source ⊆ U ∧ (Q : E → E) = f ∧
      ContDiffOn ℝ ∞ Q Q.source ∧ ContDiffOn ℝ ∞ Q.symm Q.target := by
  have hfp := hf.contDiffAt (hU.mem_nhds hp)
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ f p)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hd : HasFDerivAt f A.toContinuousLinearMap p :=
    (hfp.differentiableAt (by simp)).hasFDerivAt
  have hu : ∀ᶠ z in 𝓝 p, IsUnit (fderiv ℝ f z) :=
    (hfp.continuousAt_fderiv (by simp)).eventually
      (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr hbij))
  obtain ⟨W, hWU, hW, hpW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hp) hu)
  let Q := (hfp.toOpenPartialHomeomorph f hd (by simp)).restr W
  have hQf : (Q : E → E) = f := rfl
  have hQW : Q.source ⊆ W := fun _ hz => interior_subset hz.2
  refine ⟨Q, ?_, fun z hz => (hWU (hQW hz)).1, hQf, ?_, ?_⟩
  · exact ⟨hfp.mem_toOpenPartialHomeomorph_source hd (by simp),
      by simpa only [hW.interior_eq] using hpW⟩
  · exact hf.mono (fun z hz => (hWU (hQW hz)).1)
  · intro y hy
    have hz := hQW (Q.symm.map_source hy)
    have hF := hf.contDiffAt (hU.mem_nhds (hWU hz).1)
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp (hWU hz).2
    let B := ContinuousLinearEquiv.ofBijective (fderiv ℝ f (Q.symm y))
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    have hDF : HasFDerivAt Q B.toContinuousLinearMap (Q.symm y) :=
      (hF.differentiableAt (by simp)).hasFDerivAt
    exact (Q.contDiffAt_symm hy hDF hF).contDiffWithinAt

private theorem exists_smooth_euclidean_parameterInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} (hU : IsOpen U) {f : ℝ × E → E}
    (hf : ContDiffOn ℝ ∞ f U) {s : ℝ} {p : E} (hp : (s, p) ∈ U)
    (hi : ∀ᶠ y in 𝓝 p, f (s, y) = y) :
    ∃ (W : Set (ℝ × E)) (ψ : ℝ × E → E), IsOpen W ∧ (s, p) ∈ W ∧
      ContDiffOn ℝ ∞ ψ W ∧
      ∀ z ∈ W, (z.1, ψ z) ∈ U ∧ f (z.1, ψ z) = z.2 := by
  let F : ℝ × E → ℝ × E := fun z => (z.1, f z)
  have hF : ContDiffOn ℝ ∞ F U := contDiff_fst.contDiffOn.prodMk hf
  have hFd := (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  let A := fderiv ℝ F (s, p)
  have hfst (z : ℝ × E) : (A z).1 = z.1 := by
    have h := hFd.hasFDerivAt.fst.unique (hasFDerivAt_fst (p := (s, p)))
    exact congrArg (fun L : (ℝ × E) →L[ℝ] ℝ => L z) h
  have hvertical (v : E) : A (0, v) = (0, v) := by
    have hin : HasFDerivAt (fun y : E => (s, y))
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p :=
      (hasFDerivAt_const s p).prodMk (hasFDerivAt_id p)
    have heq : (fun y => F (s, y)) =ᶠ[𝓝 p] (fun y => (s, y)) :=
      hi.mono (fun y hy => Prod.ext rfl hy)
    have h := (hFd.hasFDerivAt.comp p hin).unique
      (hin.congr_of_eventuallyEq heq)
    exact congrArg (fun L : E →L[ℝ] (ℝ × E) => L v) h
  have hshape (r : ℝ) (v : E) : A (r, v) = (r, (A (r, 0)).2 + v) := by
    have hz : (r, v) = (r, 0) + (0, v) := by simp
    rw [hz, map_add, hvertical]
    exact Prod.ext (by simpa using hfst (r, 0)) rfl
  have hbij : Function.Bijective A := by
    constructor
    · rintro ⟨r, v⟩ ⟨t, w⟩ he
      have hrt : r = t := by simpa only [hfst] using congrArg Prod.fst he
      subst t
      rw [hshape r v, hshape r w] at he
      exact Prod.ext rfl (add_left_cancel (congrArg Prod.snd he))
    · rintro ⟨r, v⟩
      exact ⟨(r, v - (A (r, 0)).2), by rw [hshape]; simp⟩
  obtain ⟨Q, hpQ, hQU, hQF, _, hQi⟩ :=
    exists_smooth_euclidean_localInverse hU hF hp hbij
  have hfix : F (s, p) = (s, p) := Prod.ext rfl (hi.self_of_nhds)
  refine ⟨Q.target, fun z => (Q.symm z).2, Q.open_target, ?_, hQi.snd, ?_⟩
  · simpa only [hQF, hfix] using Q.map_source hpQ
  · intro z hz
    have hq := Q.right_inv hz
    rw [hQF] at hq
    have ht : (Q.symm z).1 = z.1 := by simpa only [F] using congrArg Prod.fst hq
    have hpU := hQU (Q.symm.map_source hz)
    have hv : f (Q.symm z) = z.2 := congrArg Prod.snd hq
    simpa only [← ht, Prod.mk.eta] using And.intro hpU hv

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_spatial_rightInverse_near_initial
    {J : Set ℝ} {V : Set M} (hJ : IsOpen J) (hV : IsOpen V)
    {Φ : ℝ × M → M}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (J ×ˢ V))
    {s : ℝ} (hs : s ∈ J) (hinit : ∀ y ∈ V, Φ (s, y) = y)
    {p : M} (hp : p ∈ V) :
    ∃ (W : Set (ℝ × M)) (ψ : ℝ × M → M),
      IsOpen W ∧ (s, p) ∈ W ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ ψ W ∧
      ∀ z ∈ W, z.1 ∈ J ∧ ψ z ∈ V ∧ Φ (z.1, ψ z) = z.2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := p) (n := ∞))
  let κ : ℝ × E → ℝ × M := fun z => (z.1, c.symm z.2)
  let D : Set (ℝ × E) := univ ×ˢ c.target
  have hD : IsOpen D := isOpen_univ.prod (isOpen_extChartAt_target p)
  have hκ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ κ D := by
    apply contDiff_fst.contMDiff.contMDiffOn.prodMk
    exact (contMDiffOn_extChartAt_symm p).comp contDiff_snd.contMDiff.contMDiffOn
      (fun z hz => hz.2)
  let D₁ := D ∩ κ ⁻¹' (J ×ˢ V)
  have hD₁ : IsOpen D₁ := hκ.continuousOn.isOpen_inter_preimage hD (hJ.prod hV)
  have hP : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ (Φ ∘ κ) D₁ :=
    hΦ.comp (hκ.mono inter_subset_left) (fun z hz => hz.2)
  let U := D₁ ∩ (Φ ∘ κ) ⁻¹' c.source
  have hU : IsOpen U := hP.continuousOn.isOpen_inter_preimage hD₁
    (isOpen_extChartAt_source p)
  let f : ℝ × E → E := fun z => c (Φ (κ z))
  have hf : ContDiffOn ℝ ∞ f U :=
    (hc.comp (hP.mono inter_subset_left)
      (fun z hz => hz.2)).contDiffOn
  have hcp : c.symm (c p) = p := c.left_inv (mem_extChartAt_source p)
  have hpU : (s, c p) ∈ U := by
    refine ⟨⟨⟨mem_univ _, mem_extChartAt_target p⟩, ?_⟩, ?_⟩
    · change (s, c.symm (c p)) ∈ J ×ˢ V
      rw [hcp]
      exact ⟨hs, hp⟩
    · change Φ (s, c.symm (c p)) ∈ c.source
      rw [hcp, hinit p hp]
      exact mem_extChartAt_source p
  have hi : ∀ᶠ y in 𝓝 (c p), f (s, y) = y := by
    have hcs : ContinuousAt c.symm (c p) :=
      continuousAt_extChartAt_symm p
    have hVn : ∀ᶠ y in 𝓝 (c p), c.symm y ∈ V :=
      hcs.preimage_mem_nhds (by rw [hcp]; exact hV.mem_nhds hp)
    filter_upwards [hVn, (isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds
      (mem_extChartAt_target p)] with y hy hyt
    change c (Φ (s, c.symm y)) = y
    rw [hinit _ hy, c.right_inv hyt]
  obtain ⟨W₀, ψ₀, hW₀, hpW₀, hψ₀, hright⟩ :=
    exists_smooth_euclidean_parameterInverse hU hf hpU hi
  let C : Set (ℝ × M) := univ ×ˢ c.source
  let χ : ℝ × M → ℝ × E := fun z => (z.1, c z.2)
  have hC : IsOpen C := isOpen_univ.prod (isOpen_extChartAt_source p)
  have hχ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ × E) ∞ χ C := by
    exact contMDiff_fst.contMDiffOn.prodMk_space
      (hc.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2))
  let W := C ∩ χ ⁻¹' W₀
  let ψ : ℝ × M → M := fun z => c.symm (ψ₀ (χ z))
  have hW : IsOpen W := hχ.continuousOn.isOpen_inter_preimage hC hW₀
  have hright' (z : ℝ × M) (hz : z ∈ W) :
      (z.1, ψ₀ (χ z)) ∈ U ∧ f (z.1, ψ₀ (χ z)) = c z.2 :=
    hright (χ z) hz.2
  refine ⟨W, ψ, hW, ⟨⟨mem_univ _, mem_extChartAt_source p⟩, hpW₀⟩, ?_, ?_⟩
  · apply (contMDiffOn_extChartAt_symm p).comp
      (hψ₀.contMDiffOn.comp (hχ.mono inter_subset_left) (fun z hz => hz.2))
    intro z hz
    exact (hright' z hz).1.1.1.2
  · intro z hz
    have hr := hright' z hz
    refine ⟨hr.1.1.2.1, hr.1.1.2.2, ?_⟩
    have hv := congrArg c.symm hr.2
    change c.symm (c (Φ (z.1, ψ z))) = c.symm (c z.2) at hv
    have hsource : Φ (z.1, ψ z) ∈ c.source := hr.1.2
    rw [c.left_inv hsource, c.left_inv hz.1.2] at hv
    exact hv

end Poincare.Manifold
