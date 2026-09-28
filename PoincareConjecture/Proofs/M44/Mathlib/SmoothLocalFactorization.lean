import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

theorem exists_smooth_local_chart_factorization
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (E n) M]
    [IsManifold 𝓘(ℝ, E n) ∞ M]
    {f : E n → M} {V : Set (E n)} {R : Set M}
    (hV : IsOpen V) (hR : IsOpen R)
    (hf : ContMDiffOn 𝓘(ℝ, E n) 𝓘(ℝ, E n) ∞ f V) (hmap : MapsTo f V R)
    {x : E n} (hx : x ∈ V) :
    ∃ U W : Set (E n), IsOpen U ∧ IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      U ⊆ (extChartAt 𝓘(ℝ, E n) (f x)).target ∧
      (extChartAt 𝓘(ℝ, E n) (f x)).symm '' U ⊆ R ∧
      ∃ k : E n → E n, ContDiffOn ℝ ∞ k W ∧ MapsTo k W U ∧
        ∀ y ∈ W, f y = (extChartAt 𝓘(ℝ, E n) (f x)).symm (k y) := by
  let q := f x
  let z := extChartAt 𝓘(ℝ, E n) q q
  have hz : z ∈ (extChartAt 𝓘(ℝ, E n) q).target := mem_extChartAt_target q
  have hinv := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E n)) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hz)
  have hroot : (extChartAt 𝓘(ℝ, E n) q).symm z = q := extChartAt_to_inv q
  have hRpre : (extChartAt 𝓘(ℝ, E n) q).symm ⁻¹' R ∈ 𝓝 z :=
    hinv.continuousAt.preimage_mem_nhds (hR.mem_nhds (by rw [hroot]; exact hmap hx))
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_extChartAt_target q).mem_nhds hz) hRpre)
  let U := Metric.ball z epsilon
  have hUT : U ⊆ (extChartAt 𝓘(ℝ, E n) q).target := fun _ hy => (hball hy).1
  have hUR : (extChartAt 𝓘(ℝ, E n) q).symm '' U ⊆ R := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hball hy).2
  let k := (extChartAt 𝓘(ℝ, E n) q) ∘ f
  have hfx := hf.contMDiffAt (hV.mem_nhds hx)
  have hkx : ContMDiffAt 𝓘(ℝ, E n) 𝓘(ℝ, E n) ∞ k x :=
    (contMDiffAt_extChartAt (I := 𝓘(ℝ, E n)) (x := q)).comp x hfx
  have hknhds : k ⁻¹' U ∈ 𝓝 x := hkx.continuousAt.preimage_mem_nhds
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hepsilon))
  have hfnhds : f ⁻¹' (extChartAt 𝓘(ℝ, E n) q).source ∈ 𝓝 x :=
    hfx.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds q)
  obtain ⟨delta, hdelta, hsmall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hV.mem_nhds hx) (inter_mem hfnhds hknhds))
  let W := Metric.ball x delta
  have hWV : W ⊆ V := fun _ hy => (hsmall hy).1
  have hfW : MapsTo f W (chartAt (E n) q).source := by
    intro y hy
    have h := (hsmall hy).2.1
    rwa [extChartAt_source] at h
  have hkW : ContDiffOn ℝ ∞ k W := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact (contMDiffOn_extChartAt (I := 𝓘(ℝ, E n)) (x := q)).comp (hf.mono hWV) hfW
  refine ⟨U, W, Metric.isOpen_ball, Metric.isOpen_ball, Metric.mem_ball_self hdelta,
    hWV, hUT, hUR, k, hkW, fun _ hy => (hsmall hy).2.2, ?_⟩
  intro y hy
  exact ((extChartAt 𝓘(ℝ, E n) q).left_inv ((hsmall hy).2.1)).symm

end Poincare
