import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Polar.Inverse

/-! A concrete local lift of the fixed second geodesic through a polar inverse.
Source: MT Claim 19.41, p. 471; short-geodesic-digons derivation, Section 8.
This constructs the local perturbation map but does not assert confinement. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareMT

/-- A regular polar preimage gives an actual smooth local lift of any
smooth curve through its image, retaining the chosen preimage and equality
on a full parameter neighborhood.
Source: MT Claim 19.41, p. 471; digon derivation, Section 8. -/
theorem m64Intrinsic_exists_local_polar_curve_lift
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    {v : AnnulusCoordinates} (hv : v ∈ Omega)
    (hreg : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e v))
    {beta : ℝ → AnnulusCoordinates} {s : ℝ} (hb : ContDiffAt ℝ ∞ beta s)
    (hpoint : e v = beta s) :
    ∃ u : ℝ → AnnulusCoordinates,
      ContDiffAt ℝ ∞ u s ∧ u s = v ∧
      (∀ᶠ a in 𝓝 s, u a ∈ Omega ∧ e (u a) = beta a) := by
  obtain ⟨F, hvF, hFO, hF, _, hFi⟩ :=
    m64Intrinsic_exists_smooth_polar_inverse hOmega he hv hreg
  have hsF : beta s ∈ F.target := by
    rw [← hpoint, ← hF]
    exact F.map_source hvF
  let u : ℝ → AnnulusCoordinates := F.symm ∘ beta
  have hu : ContDiffAt ℝ ∞ u s :=
    (hFi.contDiffAt (F.open_target.mem_nhds hsF)).comp s hb
  have hu0 : u s = v := by
    change F.symm (beta s) = v
    rw [← hpoint, ← hF, F.left_inv hvF]
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hb.continuousAt.preimage_mem_nhds (F.open_target.mem_nhds hsF)] with a ha
  refine ⟨hFO (F.map_target ha), ?_⟩
  change e (F.symm (beta a)) = beta a
  rw [← hF]
  exact F.right_inv ha

end PoincareMT
