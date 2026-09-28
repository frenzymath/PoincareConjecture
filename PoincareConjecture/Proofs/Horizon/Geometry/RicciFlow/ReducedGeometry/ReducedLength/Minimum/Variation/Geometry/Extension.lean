import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem parametricExtension_differentiableAt_time {I : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (E : ParametricAlongCurveExtensionOn I γ Y) {s : ℝ} {x : M}
    (h : (s, x) ∈ E.domain) : DifferentiableAt ℝ (fun r ↦ E.extension r x) s := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hmap := (E.smooth _ h).contMDiffAt (E.open_domain.mem_nhds h)
  have hslice : ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x
        (E.extension r x)) s :=
    hmap.comp s (f := fun r : ℝ ↦ (r, x)) (contMDiffAt_id.prodMk contMDiffAt_const)
  have hc : ContDiffAt ℝ ∞
      (fun r ↦ e.continuousLinearMapAt ℝ x (E.extension r x)) s := by
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hx] using
      (Bundle.contMDiffAt_totalSpace.mp hslice).2.contDiffAt
  have hi := (e.symmL ℝ x).contDiff.contDiffAt.comp s hc
  simpa only [Function.comp_def, e.symmL_continuousLinearMapAt hx] using
    hi.differentiableAt (by norm_num)

theorem parametricExtension_contMDiffAt_space {I : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (E : ParametricAlongCurveExtensionOn I γ Y) {s : ℝ} {x : M}
    (h : (s, x) ∈ E.domain) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E.extension s y)) x :=
  ((E.smooth _ h).contMDiffAt (E.open_domain.mem_nhds h)).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)

theorem parametricExtension_contMDiffAt_smul_reparam {I : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (E : ParametricAlongCurveExtensionOn I γ Y) {f c : ℝ → ℝ} {z : ℝ × M}
    (h : (f z.1, z.2) ∈ E.domain)
    (hf : ContDiffAt ℝ ∞ f z.1) (hc : ContDiffAt ℝ ∞ c z.1) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
        (c w.1 • E.extension (f w.1) w.2)) z := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) z.2
  have hmap := ((E.smooth _ h).contMDiffAt (E.open_domain.mem_nhds h)).comp z
    ((hf.contMDiffAt.comp z contMDiffAt_fst).prodMk contMDiffAt_snd)
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_snd, ?_⟩
  have hcoord := (Bundle.contMDiffAt_totalSpace.mp hmap).2
  have hprod := (hc.contMDiffAt.comp z contMDiffAt_fst).smul hcoord
  apply hprod.congr_of_eventuallyEq
  have hnear : ∀ᶠ w : ℝ × M in 𝓝 z, w.2 ∈ e.baseSet :=
    continuous_snd.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hnear] with w hw
  change (e ⟨w.2, c w.1 • E.extension (f w.1) w.2⟩).2 =
    c w.1 • (e ⟨w.2, E.extension (f w.1) w.2⟩).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hw, map_smul]

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
