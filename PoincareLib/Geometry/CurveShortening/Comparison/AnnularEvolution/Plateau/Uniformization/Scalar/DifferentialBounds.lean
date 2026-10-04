import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.BoundaryDifferentialLimit
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.InverseConformal

/-!
# Uniform differential bounds for the actual covering potential

The actual physical boundary limits extend the differential continuously
over the compact closed annulus. Noncriticality in the interior follows
from the genuine inverse-cover differential identity. Compactness then
gives uniform positive lower and finite upper bounds.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- The classical differential of an actual harmonic annular potential has a continuous
extension to the closed annulus; its boundary values are nonzero by the proved radial
barriers and boundary regularity. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-cover-uniform-differential-bounds.md`. -/
theorem annular_harmonic_differential_extension
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∃ J : Plane → Plane →L[ℝ] ℝ,
      ContinuousOn J (closure scalarAnnulus) ∧ EqOn J (fderiv ℝ H) scalarAnnulus ∧
      ∀ x ∈ closure scalarAnnulus, x ∉ scalarAnnulus → J x ≠ 0 := by
  have hdc : ContinuousOn (fderiv ℝ H) scalarAnnulus :=
    (contMDiffOn_iff_contDiffOn.mp hHs).continuousOn_fderiv_of_isOpen
      scalarAnnulus_isOpen (by simp)
  have hclosed : closure scalarAnnulus ⊆ {x : Plane | 0 ≤ scalarAnnulusDefining x} :=
    closure_minimal (fun x hx => ((scalarAnnulusDefining_pos x).mpr hx).le)
      (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  have hboundary (x : Plane) (hx : x ∈ closure scalarAnnulus) (hxA : x ∉ scalarAnnulus) :
      ∃ L : Plane →L[ℝ] ℝ, L ≠ 0 ∧
        Tendsto (fderiv ℝ H) (𝓝[scalarAnnulus] x) (𝓝 L) := by
    apply annular_harmonic_fderiv_boundary_limit D hHc hHs hlap hinner houter ⟨x, hx⟩
    apply (scalarAnnulusDefining_zero x).mp
    apply le_antisymm _ (hclosed hx)
    exact le_of_not_gt (fun hp => hxA ((scalarAnnulusDefining_pos x).mp hp))
  refine ⟨extendFrom scalarAnnulus (fderiv ℝ H), ?_, extendFrom_extends hdc, ?_⟩
  · apply continuousOn_extendFrom subset_rfl
    intro x hx
    by_cases hxA : x ∈ scalarAnnulus
    · exact ⟨fderiv ℝ H x, hdc x hxA⟩
    · obtain ⟨L, -, hL⟩ := hboundary x hx hxA
      exact ⟨L, hL⟩
  · intro x hx hxA
    obtain ⟨L, hLn, hL⟩ := hboundary x hx hxA
    rwa [extendFrom_eq hx hL]

/-- Uniform positive lower and finite upper bounds follow from the actual closed
differential and interior noncriticality. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-cover-uniform-differential-bounds.md`. -/
theorem annular_harmonic_uniform_differential_bounds
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hnon : ∀ x ∈ scalarAnnulus, fderiv ℝ H x ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ x ∈ scalarAnnulus, c ≤ ‖fderiv ℝ H x‖ ∧ ‖fderiv ℝ H x‖ ≤ C := by
  obtain ⟨J, hJc, hJeq, hJn⟩ :=
    annular_harmonic_differential_extension D hHc hHs hlap hinner houter
  have hclosed : closure scalarAnnulus ⊆ {x : Plane | 0 ≤ scalarAnnulusDefining x} :=
    closure_minimal (fun x hx => ((scalarAnnulusDefining_pos x).mpr hx).le)
      (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  have hK : IsCompact (closure scalarAnnulus) :=
    scalarClosedAnnulus_isCompact.of_isClosed_subset isClosed_closure hclosed
  have hKne : (closure scalarAnnulus).Nonempty :=
    scalarAnnulus_isConnected.nonempty.mono subset_closure
  have hpos (x : Plane) (hx : x ∈ closure scalarAnnulus) : 0 < ‖J x‖ := by
    apply norm_pos_iff.mpr
    by_cases hxA : x ∈ scalarAnnulus
    · rw [hJeq hxA]
      exact hnon x hxA
    · exact hJn x hx hxA
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne hJc.norm
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne hJc.norm
  refine ⟨‖J a‖, ‖J b‖, hpos a ha, hpos b hb, ?_⟩
  intro x hx
  rw [← hJeq hx]
  exact ⟨hmin (subset_closure hx), hmax (subset_closure hx)⟩

/-- The genuine normalized covering chart supplies its interior noncriticality directly, so
its uniform differential bounds require no additional noncriticality or boundary regularity
hypothesis. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-cover-uniform-differential-bounds.md`. -/
theorem scalar_cover_potential_uniform_differential_bounds
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ x ∈ scalarAnnulus, c ≤ ‖fderiv ℝ H x‖ ∧ ‖fderiv ℝ H x‖ ≤ C := by
  apply annular_harmonic_uniform_differential_bounds D hHc hHs hlap hinner houter
  intro x hx hzero
  obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjOn hx
  have hzs : z ∈ e.source := hsource ▸ hz
  have hy := e.map_source hzs
  have hc := congrArg Prod.fst
    (scalarInverseCoverMap_coordinates D hHs hdV P e hsource he hes hei hy (1, 0))
  simp only [scalarInverseCoverMap, Function.comp_apply, e.left_inv hzs, hzero, zero_apply] at hc
  norm_num at hc

end PoincareMT.M64Uniformization
