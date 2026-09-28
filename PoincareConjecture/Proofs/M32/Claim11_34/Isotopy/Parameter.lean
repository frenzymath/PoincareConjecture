import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Maps.Proper.Basic

















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32




private theorem trace_isClosedEmbedding
    {P Y : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace Y] [T2Space Y] {F : ℝ × P → Y}
    (hF : Continuous F) (hinj : ∀ t, Function.Injective (fun q => F (t, q))) :
    Topology.IsClosedEmbedding (fun z : ℝ × P => (z.1, F z)) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_fst.prodMk hF)
  · rintro ⟨t, q⟩ ⟨s, r⟩ he
    have hts : t = s := congrArg Prod.fst he
    subst s
    exact Prod.ext rfl (hinj t (congrArg Prod.snd he))
  · intro C hC
    let D : Set ((ℝ × Y) × P) :=
      {z | (z.1.1, z.2) ∈ C ∧ F (z.1.1, z.2) = z.1.2}
    have hD : IsClosed D :=
      (hC.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
        (isClosed_eq (hF.comp (continuous_fst.fst.prodMk continuous_snd))
          continuous_fst.snd)
    have himage : Prod.fst '' D = (fun z : ℝ × P => (z.1, F z)) '' C := by
      ext z
      constructor
      · rintro ⟨⟨z, q⟩, ⟨hz, he⟩, rfl⟩
        exact ⟨(z.1, q), hz, Prod.ext rfl he⟩
      · rintro ⟨⟨t, q⟩, hq, rfl⟩
        exact ⟨((t, F (t, q)), q), ⟨hq, rfl⟩, rfl⟩
    rw [← himage]
    exact isClosedMap_fst_of_compactSpace D hD




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
    ∃ Q : OpenPartialHomeomorph (ℝ × E) (ℝ × E),
      (s, p) ∈ Q.source ∧ Q.source ⊆ U ∧
      (Q : ℝ × E → ℝ × E) = (fun z => (z.1, f z)) ∧
      ContDiffOn ℝ ∞ Q Q.source ∧ ContDiffOn ℝ ∞ Q.symm Q.target := by
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
  exact exists_smooth_euclidean_localInverse hU hF hp hbij

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]





theorem exists_smooth_local_sphere_parameter
    {F : ℝ × UnitTwoSphere → M}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ F)
    (hembed : ∀ t, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => F (t, q)))
    {U : Set M} (hU : IsOpen U) (hFU : ∀ t, range (fun q => F (t, q)) ⊆ U)
    (s : ℝ) (q₀ : UnitTwoSphere) :
    ∃ (W : Set (ℝ × M)) (r : ℝ × M → UnitTwoSphere),
      IsOpen W ∧ (s, F (s, q₀)) ∈ W ∧ W ⊆ univ ×ˢ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 2) ∞ r W ∧
      ∀ t q, (t, F (t, q)) ∈ W → r (t, F (t, q)) = q := by
  let h := (hembed s).isImmersion.isImmersionAt q₀
  let a := h.domChart
  let b := h.codChart
  let L := h.equiv
  let E := EuclideanSpace ℝ (Fin 3)
  have hai : ContMDiffOn (𝓡 2) (𝓡 2) ∞ a.symm a.target :=
    contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
  have hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source :=
    contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
  have hq₀ : q₀ ∈ a.source := h.mem_domChart_source
  have hFq₀ : F (s, q₀) ∈ b.source := h.mem_codChart_source
  have hchart (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ a.target) :
      b (F (s, a.symm z)) = L (z, 0) := by
    exact h.writtenInCharts (by simpa using hz)
  let y₀ : E := b (F (s, q₀))
  have hy₀ : y₀ = L (a q₀, 0) := by
    simpa only [a.left_inv hq₀] using hchart (a q₀) (a.map_source hq₀)
  let D₀ : Set (ℝ × E) := {z | (L.symm z.2).1 ∈ a.target}
  let κ : ℝ × E → ℝ × UnitTwoSphere := fun z => (z.1, a.symm (L.symm z.2).1)
  have hproj : ContDiff ℝ ∞ (fun z : ℝ × E => (L.symm z.2).1) :=
    (L.symm.contDiff.comp contDiff_snd).fst
  have hD₀ : IsOpen D₀ := a.open_target.preimage hproj.continuous
  have hκ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ κ D₀ := by
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hai.comp hproj.contMDiff.contMDiffOn (fun z hz => hz))
  have hFK : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 3) ∞ (F ∘ κ) D₀ :=
    hF.comp_contMDiffOn hκ
  let D := D₀ ∩ (F ∘ κ) ⁻¹' b.source
  have hD : IsOpen D := hFK.continuousOn.isOpen_inter_preimage hD₀ b.open_source
  let φ : ℝ × E → E := fun z => b (F (κ z)) + L (0, (L.symm z.2).2)
  have hφ : ContDiffOn ℝ ∞ φ D := by
    apply ((hb.comp (hFK.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn).add
    exact (L.contDiff.comp
      (contDiff_const.prodMk (L.symm.contDiff.comp contDiff_snd).snd)).contDiffOn
  have hsD : (s, y₀) ∈ D := by
    constructor
    · change (L.symm y₀).1 ∈ a.target
      rw [hy₀, L.symm_apply_apply]
      exact a.map_source hq₀
    · change F (s, a.symm (L.symm y₀).1) ∈ b.source
      rw [hy₀, L.symm_apply_apply, a.left_inv hq₀]
      exact hFq₀
  have hi : ∀ᶠ y in 𝓝 y₀, φ (s, y) = y := by
    have hnear : ∀ᶠ y in 𝓝 y₀, (s, y) ∈ D :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (hD.mem_nhds hsD)
    filter_upwards [hnear] with y hy
    change b (F (s, a.symm (L.symm y).1)) + L (0, (L.symm y).2) = y
    rw [hchart _ hy.1, ← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using L.apply_symm_apply y
  obtain ⟨Q, hsQ, hQD, hQφ, _, hQi⟩ :=
    exists_smooth_euclidean_parameterInverse hD hφ hsD hi
  have hbase_target : (s, y₀) ∈ Q.target := by
    simpa only [hQφ, hi.self_of_nhds] using Q.map_source hsQ

  let j : ℝ × UnitTwoSphere → ℝ × M := fun z => (z.1, F z)
  have hj : Topology.IsClosedEmbedding j :=
    trace_isClosedEmbedding hF.continuous (fun t => (hembed t).isEmbedding.injective)
  let η : ℝ × UnitTwoSphere → ℝ × E := fun z => (z.1, L (a z.2, 0))
  let A : Set (ℝ × UnitTwoSphere) := univ ×ˢ a.source
  have hA : IsOpen A := isOpen_univ.prod a.open_source
  have hη : ContinuousOn η A :=
    continuous_fst.continuousOn.prodMk
      (L.continuous.comp_continuousOn
        ((a.continuousOn.comp continuous_snd.continuousOn (fun z hz => hz.2)).prodMk
          continuous_const.continuousOn))
  let O := A ∩ η ⁻¹' Q.source
  have hO : IsOpen O := hη.isOpen_inter_preimage hA Q.open_source
  have hsO : (s, q₀) ∈ O := by
    refine ⟨⟨mem_univ _, hq₀⟩, ?_⟩
    change (s, L (a q₀, 0)) ∈ Q.source
    rwa [← hy₀]
  have htrace (z : ℝ × UnitTwoSphere) (hz : z ∈ O) :
      Q (η z) = (z.1, b (F z)) := by
    rw [hQφ]
    change (z.1, b (F (z.1, a.symm (L.symm (L (a z.2, 0))).1)) +
      L (0, (L.symm (L (a z.2, 0))).2)) = (z.1, b (F z))
    simp only [L.symm_apply_apply, a.left_inv hz.1.2, Prod.mk.eta]
    change (z.1, b (F z) + L 0) = (z.1, b (F z))
    rw [map_zero, add_zero]
  let W₀ : Set (ℝ × M) := (j '' Oᶜ)ᶜ
  have hW₀ : IsOpen W₀ := (hj.isClosedMap _ hO.isClosed_compl).isOpen_compl
  have hsW₀ : j (s, q₀) ∈ W₀ := by
    rintro ⟨z, hz, he⟩
    exact hz (hj.injective he ▸ hsO)
  let C : Set (ℝ × M) := univ ×ˢ b.source
  let χ : ℝ × M → ℝ × E := fun z => (z.1, b z.2)
  have hC : IsOpen C := isOpen_univ.prod b.open_source
  have hχ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × E) ∞ χ C :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (hb.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2))
  let W := W₀ ∩ (univ ×ˢ U) ∩ (C ∩ χ ⁻¹' Q.target)
  have hW : IsOpen W :=
    (hW₀.inter (isOpen_univ.prod hU)).inter
      (hχ.continuousOn.isOpen_inter_preimage hC Q.open_target)
  let r : ℝ × M → UnitTwoSphere := fun z => a.symm (L.symm (Q.symm (χ z)).2).1
  have hvalue (z : ℝ × M) (hz : z ∈ W) :
      (L.symm (Q.symm (χ z)).2).1 ∈ a.target :=
    (hQD (Q.symm.map_source hz.2.2)).1
  have hrec : ContDiffOn ℝ ∞
      (fun z : ℝ × E => (L.symm (Q.symm z).2).1) Q.target :=
    (L.symm.contDiff.comp_contDiffOn hQi.snd).fst
  refine ⟨W, r, hW, ?_, fun z hz => hz.1.2, ?_, ?_⟩
  · exact ⟨⟨hsW₀, ⟨mem_univ _, hFU s ⟨q₀, rfl⟩⟩⟩,
      ⟨⟨mem_univ _, hFq₀⟩, hbase_target⟩⟩
  · exact hai.comp
      (hrec.contMDiffOn.comp (hχ.mono (fun z (hz : z ∈ W) => hz.2.1))
        (fun z hz => hz.2.2)) hvalue
  · intro t q hz
    have htq : (t, q) ∈ O := by
      by_contra hn
      exact hz.1.1 ⟨(t, q), hn, rfl⟩
    have hleft : Q.symm (χ (t, F (t, q))) = η (t, q) := by
      change Q.symm (t, b (F (t, q))) = η (t, q)
      rw [← htrace (t, q) htq]
      exact Q.left_inv htq.2
    change a.symm (L.symm (Q.symm (χ (t, F (t, q)))).2).1 = q
    rw [hleft]
    change a.symm (L.symm (L (a q, 0))).1 = q
    rw [L.symm_apply_apply]
    exact a.left_inv htq.1.2

end PoincareConjecture.M32
