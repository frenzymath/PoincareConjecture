import PoincareConjecture.Proofs.M14.Sec6_2_ProjectionCoordinates
import PoincareConjecture.Proofs.M14.Mathlib.MovingLinearMap
import PoincareConjecture.Proofs.M08.VariationCoordinates

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

noncomputable def surfaceHorizontalFst (α : ℝ × ℝ → G.Point) (s u : ℝ) :
    G.Horizontal (α (s, u)) :=
  G.spacetime.horizontalProjection (α (s, u))
    (mfderiv 𝓘(ℝ) (spacetimeModel n) (fun r => α (r, u)) s (1 : ℝ))

noncomputable def surfaceHorizontalSnd (α : ℝ × ℝ → G.Point) (s u : ℝ) :
    G.Horizontal (α (s, u)) :=
  G.spacetime.horizontalProjection (α (s, u))
    (mfderiv 𝓘(ℝ) (spacetimeModel n) (fun r => α (s, r)) u (1 : ℝ))

set_option maxHeartbeats 2000000 in

theorem horizontalCovariantDerivative_surface_commute
    (hCoordinates : M12MetricPredecessors.{0} n)
    {α : ℝ × ℝ → G.Point} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hα : ContMDiffOn ((𝓘(ℝ)).prod 𝓘(ℝ)) (spacetimeModel n) ∞ α Ω)
    {s u : ℝ} (hp : (s, u) ∈ Ω) {J K : Set ℝ}
    (hJ : J ∈ 𝓝 s) (hK : K ∈ 𝓝 u)
    (ES : M14PullbackExtension G (fun r => α (r, u)) J
      (fun r => surfaceHorizontalSnd α r u))
    (EU : M14PullbackExtension G (fun r => α (s, r)) K
      (fun r => surfaceHorizontalFst α s r)) :
    M14HorizontalCovariantDerivative G (fun r => α (r, u)) J
        (fun r => surfaceHorizontalSnd α r u) ES s =
      M14HorizontalCovariantDerivative G (fun r => α (s, r)) K
        (fun r => surfaceHorizontalFst α s r) EU u := by
  let x := α (s, u)
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let c := extChartAt (spacetimeModel n) x
  let O := Ω ∩ α ⁻¹' (c.source ∩ e.baseSet)
  let z := c ∘ α
  let a := fun r => deriv (fun v => z (r, v)) u
  let b := fun v => deriv (fun r => z (r, v)) s
  have hO : IsOpen O := hα.continuousOn.isOpen_inter_preimage hΩ
    ((isOpen_extChartAt_source (I := spacetimeModel n) x).inter e.open_baseSet)
  have hx : x ∈ c.source := mem_extChartAt_source x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hpO : (s, u) ∈ O := ⟨hp, hx, he⟩
  have hA (q : ℝ × ℝ) (hq : q ∈ O) :
      MDifferentiableAt ((𝓘(ℝ)).prod 𝓘(ℝ)) (spacetimeModel n) α q :=
    (hα.contMDiffAt (hΩ.mem_nhds hq.1)).mdifferentiableAt (by simp)
  have hz : ContDiffOn ℝ ∞ z O := by
    intro q hq
    have hc : ContMDiffAt (spacetimeModel n) 𝓘(ℝ, SpacetimeModelVector n) ∞ c (α q) :=
      contMDiffAt_extChartAt' (I := spacetimeModel n) (n := ∞)
        (by simpa only [c, extChartAt_source] using hq.2.1)
    have h := hc.comp q (hα.contMDiffAt (hΩ.mem_nhds hq.1))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt.contDiffWithinAt
  obtain ⟨k, hb, ha⟩ := M08.coordinate_mixed_hasDerivAt hO z hz hpO
  have hsA : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) (fun r => α (r, u)) s :=
    (hA _ hpO).comp s (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have huA : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) (fun v => α (s, v)) u :=
    (hA _ hpO).comp u (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hC := (horizontalProjectionInCoordinates_contMDiffAt e hx he).mdifferentiableAt
    (by simp)
  have hsderiv := moving_linearMap_comp_hasDerivAt hC hsA ha
  have huderiv := moving_linearMap_comp_hasDerivAt hC huA hb
  have hnearS : ∀ᶠ r in 𝓝 s, (r, u) ∈ O :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hO.mem_nhds hpO)
  have hnearU : ∀ᶠ v in 𝓝 u, (s, v) ∈ O :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hO.mem_nhds hpO)
  have hsfield : (fun r => e.continuousLinearMapAt ℝ (α (r, u))
      (surfaceHorizontalSnd α r u)) =ᶠ[𝓝 s]
        (fun r => horizontalProjectionInCoordinates e x (α (r, u)) (a r)) := by
    filter_upwards [hnearS] with r hr
    exact (horizontalProjectionInCoordinates_curve_deriv e hr.2.1
      ((hA _ hr).comp u (mdifferentiableAt_const.prodMk mdifferentiableAt_id))).symm
  have hufield : (fun v => e.continuousLinearMapAt ℝ (α (s, v))
      (surfaceHorizontalFst α s v)) =ᶠ[𝓝 u]
        (fun v => horizontalProjectionInCoordinates e x (α (s, v)) (b v)) := by
    filter_upwards [hnearU] with v hv
    exact (horizontalProjectionInCoordinates_curve_deriv e hv.2.1
      ((hA _ hv).comp s (mdifferentiableAt_id.prodMk mdifferentiableAt_const))).symm
  have hscoord := horizontalCovariantDerivative_coordinates e ES (mem_of_mem_nhds hJ) he
    (uniqueDiffWithinAt_of_mem_nhds hJ) hsA.mdifferentiableWithinAt
  have hucoord := horizontalCovariantDerivative_coordinates e EU (mem_of_mem_nhds hK) he
    (uniqueDiffWithinAt_of_mem_nhds hK) huA.mdifferentiableWithinAt
  rw [(hsderiv.congr_of_eventuallyEq hsfield).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_of_mem_nhds hJ)] at hscoord
  rw [(huderiv.congr_of_eventuallyEq hufield).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_of_mem_nhds hK)] at hucoord
  have hsvel : VectorField.chartFrame (spacetimeModel n) x (b u) x =
      mfderiv 𝓘(ℝ) (spacetimeModel n) (fun r => α (r, u)) s (1 : ℝ) :=
    VectorField.chartFrame_curve_deriv (spacetimeModel n)
      (by simpa only [c, extChartAt_source] using hx) hsA
  have huvel : VectorField.chartFrame (spacetimeModel n) x (a s) x =
      mfderiv 𝓘(ℝ) (spacetimeModel n) (fun v => α (s, v)) u (1 : ℝ) :=
    VectorField.chartFrame_curve_deriv (spacetimeModel n)
      (by simpa only [c, extChartAt_source] using hx) huA
  have hsval : surfaceHorizontalSnd α s u = horizontalChartFrame x (a s) x :=
    congrArg (G.spacetime.horizontalProjection x) huvel.symm
  have huval : surfaceHorizontalFst α s u = horizontalChartFrame x (b u) x :=
    congrArg (G.spacetime.horizontalProjection x) hsvel.symm
  have ht := horizontalProjectionInCoordinates_torsion e hCoordinates hx he (a s) (b u)
  apply (e.continuousLinearEquivAt ℝ x he).injective
  simp only [e.coe_continuousLinearEquivAt_eq he]
  rw [hscoord, hucoord]
  simp only [mfderivWithin_of_mem_nhds hJ, mfderivWithin_of_mem_nhds hK]
  rw [hsval, huval, ← hsvel, ← huvel]
  have hsum := congrArg (fun v => v + horizontalProjectionInCoordinates e x x k) ht
  convert! hsum using 1 <;> abel

end PoincareConjecture.M14
