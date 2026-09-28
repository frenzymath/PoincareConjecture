import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.KernelLeafConstancy

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eventuallyEq_affineLeaf_extension (a : F →ᴬ[ℝ] E)
    (Q : F → E →L[ℝ] F) (x0 : F)
    (hnorm : ∀ x, Function.RightInverse a.contLinear (Q x))
    (e : OpenPartialHomeomorph (F × (Q x0).ker) E)
    (he : (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0)
    {x : F} (hsource : (x, 0) ∈ e.source) {G : E → E →L[ℝ] F} {V : Set E}
    (hV : V ∈ 𝓝 (a x)) (hG : ContinuousOn G V)
    (hleaf : ∀ z ∈ V, ∀ᶠ w in 𝓝 z, w - z ∈ (G z).ker → G w = G z)
    (hslice : (fun v => G (a v)) =ᶠ[𝓝 x] Q) :
    G =ᶠ[𝓝 (a x)] (fun y => Q (e.symm y).1) := by
  have hzero : e (x, 0) = a x := by rw [he, a.affineLeafMap_zero]
  have htarget : a x ∈ e.target := hzero ▸ e.map_source hsource
  have hinv : e.symm (a x) = (x, 0) := by
    rw [← hzero]
    exact e.left_inv hsource
  have hbase : Tendsto (fun y => (e.symm y).1) (𝓝 (a x)) (𝓝 x) := by
    simpa only [hinv] using (e.continuousAt_symm htarget).fst.tendsto
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hbaseball : ∀ᶠ y in 𝓝 (a x), a (e.symm y).1 ∈ Metric.ball (a x) r :=
    (a.continuous.continuousAt.tendsto.comp hbase)
      (Metric.ball_mem_nhds (a x) hr)
  filter_upwards [e.open_target.mem_nhds htarget, Metric.ball_mem_nhds (a x) hr,
    hbaseball, hbase.eventually hslice] with y hy hyball hbball hslice_y
  have hey : a.affineLeafMap Q x0 (e.symm y) = y := by
    rw [← he]
    exact e.right_inv hy
  have hker : y - a (e.symm y).1 ∈ (G (a (e.symm y).1)).ker := by
    rw [hslice_y]
    simpa only [hey] using a.affineLeafMap_sub_mem_ker Q x0 hnorm (e.symm y)
  exact ((hG.mono hball).eq_of_sub_mem_ker_of_convex
    (convex_ball (a x) r) (fun z hz => hleaf z (hball hz)) hbball hyball hker).trans
    hslice_y

end ContinuousAffineMap
