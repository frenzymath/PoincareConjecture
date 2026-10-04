import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.NeckHeightControlPath
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceRecutFrontier

/-!
# Continuous axial height across the actual cap core

Truncating below an interior height makes the literal end height
constant on an actual open neighborhood of the retained core. Source:
Morgan-Tian Proposition 9.79, p. 234; cap-ball-confinement.md.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

/-- The actual end height truncated from below, extended constantly
off the actual end (cap confinement, Proposition 9.79). -/
noncomputable def collarHeight (c : ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ N.end_neck.carrier then max c (N.end_neck.coordinate_inverse x).2 else c

/-- On the literal end, the extension is exactly the truncated height. -/
theorem collarHeight_of_mem_end (c : ℝ) {x : M} (hx : x ∈ N.end_neck.carrier) :
    N.collarHeight c x = max c (N.end_neck.coordinate_inverse x).2 := by
  simp only [collarHeight, if_pos hx]

/-- The whole actual inner recut has constant extended height, including
its retained core and boundary. -/
theorem collarHeight_eq_of_mem_recut {c : ℝ} {x : M} (hx : x ∈ N.recutCarrier c) :
    N.collarHeight c x = c := by
  classical
  rcases hx with hxY | hxE
  · rw [N.closed_core_eq_complement_end] at hxY
    simp only [collarHeight, if_neg hxY.2]
  · rw [N.collarHeight_of_mem_end c hxE.1, max_eq_left hxE.2.2.le]

/-- The literal truncated height is continuous across the actual core;
the proved open inner recut supplies its constant neighborhood. -/
theorem collarHeight_continuousOn {c : ℝ}
    (hc : -N.epsilon⁻¹ < c) (hc' : c < N.epsilon⁻¹) :
    ContinuousOn (N.collarHeight c) N.carrier := by
  classical
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hxE : x ∈ N.end_neck.carrier
  · have hi := N.end_neck.coordinate_inverse_smooth.continuousOn.continuousAt
      (N.end_neck.carrier_open.mem_nhds hxE)
    have heq : N.collarHeight c =ᶠ[𝓝 x]
        (fun y => max c (N.end_neck.coordinate_inverse y).2) := by
      filter_upwards [N.end_neck.carrier_open.mem_nhds hxE] with y hy
      exact N.collarHeight_of_mem_end c hy
    have hf : ContinuousAt (fun y => max c (N.end_neck.coordinate_inverse y).2) x :=
      continuousAt_const.max hi.snd
    exact hf.congr_of_eventuallyEq heq
  · have hxY : x ∈ N.closed_core := N.closed_core_eq_complement_end ▸ ⟨hx, hxE⟩
    have heq : N.collarHeight c =ᶠ[𝓝 x] (fun _ => c) := by
      filter_upwards [(N.recutCarrier_isOpen hc hc').mem_nhds (Or.inl hxY)] with y hy
      exact N.collarHeight_eq_of_mem_recut hy
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- A height strictly above the truncation threshold is a genuine point
of the old end, with exactly its actual inverse-coordinate height. -/
theorem collarHeight_above_cutoff {c : ℝ} {x : M} (hx : c < N.collarHeight c x) :
    x ∈ N.end_neck.carrier ∧ N.collarHeight c x = (N.end_neck.coordinate_inverse x).2 := by
  classical
  by_cases hxE : x ∈ N.end_neck.carrier
  · rw [N.collarHeight_of_mem_end c hxE] at hx ⊢
    have hh : c < (N.end_neck.coordinate_inverse x).2 :=
      (lt_max_iff.mp hx).resolve_left (lt_irrefl c)
    exact ⟨hxE, max_eq_right hh.le⟩
  · simp only [collarHeight, if_neg hxE, lt_self_iff_false] at hx

/-- The frontier of the actual recut has precisely its outer height
under the continuous extension. -/
theorem collarHeight_eq_of_mem_frontier {c b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) (hcb : c ≤ b)
    {x : M} (hx : x ∈ frontier (N.recutCarrier b)) : N.collarHeight c x = b := by
  obtain ⟨z, hz, rfl⟩ := N.recutCarrier_frontier_subset_axial_sphere hb hb' hx
  have hzB : z.2 = b := hz.2
  have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    simpa only [hzB, N.end_neck_epsilon, mem_Ioo] using And.intro hb hb'
  rw [N.collarHeight_of_mem_end c (N.end_neck.coordinate_map_mem_of_axial_mem hzN),
    N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem hzN, hzB, max_eq_right hcb]

end PoincareMT.CapCertificate
