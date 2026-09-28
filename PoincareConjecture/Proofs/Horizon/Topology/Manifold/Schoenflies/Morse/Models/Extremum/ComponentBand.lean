import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.LocalLevel
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.ComponentBand

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem exists_annular_continuation_of_minimum
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (e : OpenPartialHomeomorph E2 S2) {r c b : Real} (hr : 0 < r)
    (hrs : closedBall (0 : E2) r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c + ‖x‖ ^ 2)
    (hrb : c + r ^ 2 < b)
    (hunique : ∀ p, h p ∈ Icc c b ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 -> p = e 0) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (c + r ^ 2 - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (c + r ^ 2 - δ) (b + δ) -> h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, c + r ^ 2)) = e '' sphere (0 : E2) r ∧
      ∀ p ∈ e '' sphere (0 : E2) r,
        F '' (univ ×ˢ Icc (c + r ^ 2) b) =
          connectedComponentIn (h ⁻¹' Icc (c + r ^ 2) b) p := by
  have he0 : (0 : E2) ∈ e.source := hrs (mem_closedBall_self hr.le)
  have hzero : h (e 0) = c := by simpa using hform 0 he0
  have hreg (p : S2) (hp : h p ∈ Icc (c + r ^ 2) b) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0 := by
    intro hc
    have hep := hunique p ⟨by nlinarith [hp.1, sq_nonneg r], hp.2⟩ hc
    rw [hep, hzero] at hp
    nlinarith [hp.1, sq_pos_of_pos hr]
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr hr.le
  have hxs := hrs (sphere_subset_closedBall hx)
  have hxa : h (e x) = c + r ^ 2 := by rw [hform x hxs, mem_sphere_zero_iff_norm.mp hx]
  obtain ⟨δ, hδ, F, hFs, hF, hFi, hheight, hcenter, hband⟩ :=
    exists_smooth_regular_band_component_of_smooth hh hrb hreg (e x) hxa
  have hcircle : range (fun q : S1 => F (q, c + r ^ 2)) =
      e '' sphere (0 : E2) r := hcenter.trans
    (minimum_circle_eq_level_component e hr hrs hform (mem_image_of_mem _ hx)).symm
  refine ⟨δ, hδ, F, hFs, hF, hFi, hheight, hcircle, ?_⟩
  intro p hp
  have hpband : p ∈ connectedComponentIn (h ⁻¹' Icc (c + r ^ 2) b) (e x) := by
    rw [← hband]
    obtain ⟨q, hqp⟩ := hcircle ▸ hp
    exact ⟨(q, c + r ^ 2), ⟨mem_univ _, ⟨le_rfl, hrb.le⟩⟩, hqp⟩
  exact hband.trans (connectedComponentIn_eq hpband)

end Poincare.Manifold.Schoenflies
