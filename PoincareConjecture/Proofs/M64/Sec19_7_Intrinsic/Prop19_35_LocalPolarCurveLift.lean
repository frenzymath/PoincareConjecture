import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

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

end PoincareConjecture
