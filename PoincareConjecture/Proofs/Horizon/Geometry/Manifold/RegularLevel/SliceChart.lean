import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.Coordinates.FinSucc







open Set Function TopologicalSpace Poincare.EuclideanSpace
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Poincare.Geometry.Manifold.RegularLevel

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [Fact (Module.finrank ℝ E = n + 1)]
  {f : M → ℝ} (U : Opens M) (c : ℝ)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M)
  (heU : e.target ⊆ U) (hef : ∀ y ∈ e.source, f (e y) = y 0)
  (z₀ : openLevelSet f U c)

open scoped Classical in

def sliceChart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (openLevelSet f U c) where
  toFun y := if hy : euclideanCons c y ∈ e.source then
    ⟨⟨e (euclideanCons c y), heU (e.map_source hy)⟩, by
      change f (e (euclideanCons c y)) = c
      rw [hef _ hy, euclideanCons_zero]⟩ else z₀
  invFun z := euclideanTail (e.symm (openLevelIncl f U c z))
  source := euclideanCons c ⁻¹' e.source
  target := openLevelIncl f U c ⁻¹' e.target
  map_source' y hy := by
    change euclideanCons c y ∈ e.source at hy
    simp only [mem_preimage, dif_pos hy, openLevelIncl]
    exact e.map_source hy
  map_target' z hz := by
    have hs := e.map_target hz
    have hzero : e.symm (openLevelIncl f U c z) 0 = c := by
      rw [← hef _ hs, e.right_inv hz]
      exact z.2
    change euclideanCons c (euclideanTail (e.symm (openLevelIncl f U c z))) ∈ e.source
    rw [show euclideanCons c (euclideanTail (e.symm (openLevelIncl f U c z))) =
        e.symm (openLevelIncl f U c z) from by
      simpa only [hzero] using euclideanCons_tail (e.symm (openLevelIncl f U c z))]
    exact hs
  left_inv' y hy := by
    change euclideanCons c y ∈ e.source at hy
    simp only [dif_pos hy, openLevelIncl]
    rw [e.left_inv hy, euclideanTail_cons]
  right_inv' z hz := by
    have hs := e.map_target hz
    have hzero : e.symm (openLevelIncl f U c z) 0 = c := by
      rw [← hef _ hs, e.right_inv hz]
      exact z.2
    have hcons : euclideanCons c (euclideanTail (e.symm (openLevelIncl f U c z))) =
        e.symm (openLevelIncl f U c z) := by
      simpa only [hzero] using euclideanCons_tail (e.symm (openLevelIncl f U c z))
    simp only [hcons, dif_pos hs]
    apply Subtype.ext
    apply Subtype.ext
    exact e.right_inv hz
  open_source := e.open_source.preimage (contDiff_euclideanCons c).continuous
  open_target := e.open_target.preimage
    (continuous_subtype_val.comp continuous_subtype_val)
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun y : (euclideanCons c ⁻¹' e.source : Set _) =>
        e (euclideanCons c (y : EuclideanSpace ℝ (Fin n)))) :=
      e.continuousOn.comp_continuous
        ((contDiff_euclideanCons c).continuous.comp continuous_subtype_val)
        (fun y => y.2)
    have hl : Continuous (fun y : (euclideanCons c ⁻¹' e.source : Set _) =>
        (⟨⟨e (euclideanCons c (y : EuclideanSpace ℝ (Fin n))),
          heU (e.map_source y.2)⟩, by
            change f (e (euclideanCons c (y : EuclideanSpace ℝ (Fin n)))) = c
            rw [hef _ y.2, euclideanCons_zero]⟩ : openLevelSet f U c)) :=
      (hc.subtype_mk _).subtype_mk _
    convert hl using 1
    funext y
    exact dif_pos y.2
  continuousOn_invFun :=
    (continuous_euclideanTail n).comp_continuousOn
      (e.symm.continuousOn.comp
        (continuous_subtype_val.comp continuous_subtype_val).continuousOn (fun _ hz => hz))

@[simp] theorem sliceChart_source :
    (sliceChart U c e heU hef z₀).source = euclideanCons c ⁻¹' e.source := rfl

@[simp] theorem sliceChart_target :
    (sliceChart U c e heU hef z₀).target = openLevelIncl f U c ⁻¹' e.target := rfl

theorem sliceChart_apply {y : EuclideanSpace ℝ (Fin n)}
    (hy : euclideanCons c y ∈ e.source) :
    openLevelIncl f U c (sliceChart U c e heU hef z₀ y) = e (euclideanCons c y) := by
  simp only [sliceChart, OpenPartialHomeomorph.coe_mk, dif_pos hy,
    openLevelIncl]

@[simp] theorem sliceChart_symm_apply (z : openLevelSet f U c) :
    (sliceChart U c e heU hef z₀).symm z =
      euclideanTail (e.symm (openLevelIncl f U c z)) := rfl

variable (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x ∈ U, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)

theorem contMDiffOn_sliceChart (he : ContMDiffOn (𝓡 (n + 1)) I ∞ e e.source) :
    letI := openLevelSetChartedSpace hf U hreg n c
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (sliceChart U c e heU hef z₀)
      (sliceChart U c e heU hef z₀).source := by
  let := openLevelSetChartedSpace hf U hreg n c
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_into_openLevelSet_iff hf n c U hreg _ y).mpr
  have hcomp := ((he _ hy).contMDiffAt (e.open_source.mem_nhds hy)).comp y
    (contDiff_euclideanCons c).contDiffAt.contMDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [((sliceChart U c e heU hef z₀).open_source.mem_nhds hy)] with z hz
  exact sliceChart_apply U c e heU hef z₀ hz

theorem contMDiffOn_sliceChart_symm
    (he : ContMDiffOn I (𝓡 (n + 1)) ∞ e.symm e.target) :
    letI := openLevelSetChartedSpace hf U hreg n c
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (sliceChart U c e heU hef z₀).symm
      (sliceChart U c e heU hef z₀).target := by
  let := openLevelSetChartedSpace hf U hreg n c
  intro z hz
  have hcomp := ((he _ hz).contMDiffAt (e.open_target.mem_nhds hz)).comp z
    (contMDiff_openLevelIncl hf U hreg n c z)
  exact ((contDiff_euclideanTail n).contDiffAt.contMDiffAt.comp z hcomp).contMDiffWithinAt

end Poincare.Geometry.Manifold.RegularLevel
