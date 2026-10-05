import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.ConjugateClosed

/-!
# Literal classical derivatives along the two polar boundary circles

The continuous differential of the harmonic potential determines its
actual derivative within the closed polar strip. Restriction to each
boundary line gives the literal angular derivatives of both the potential
and its constructed conjugate.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

/-- The actual potential differential pulled back to polar coordinates. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-25-cover-potential-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarCoverPotentialDifferential (J : Plane → Plane →L[ℝ] ℝ) (z : Cover) :
    Cover →L[ℝ] ℝ := (J (scalarCoverMap z)).comp (fderiv ℝ scalarCoverMap z)

/-- The continuous actual differential supplies the derivative of the same potential within
the closed polar strip. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the
project construction in
`proof-work/tasks/M64/derivations/2026-09-25-cover-potential-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarCoverPotential_hasFDerivWithinAt_closure
    {H : Plane → ℝ} {J : Plane → Plane →L[ℝ] ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hJc : ContinuousOn J (closure scalarAnnulus))
    (hJeq : EqOn J (fderiv ℝ H) scalarAnnulus) {z : Cover}
    (hz : z ∈ closure scalarCoverStrip) :
    HasFDerivWithinAt (H ∘ scalarCoverMap) (scalarCoverPotentialDifferential J z)
      (closure scalarCoverStrip) z := by
  have hmaps : MapsTo scalarCoverMap (closure scalarCoverStrip) (closure scalarAnnulus) :=
    (show MapsTo scalarCoverMap scalarCoverStrip scalarAnnulus from
      fun _ hy => scalarCoverMap_mem hy).closure_of_continuousOn
        scalarCoverMap_smooth.continuous.continuousOn
  have hBc : ContinuousOn (scalarCoverPotentialDifferential J) (closure scalarCoverStrip) :=
    (hJc.comp scalarCoverMap_smooth.continuous.continuousOn hmaps).clm_comp
      (scalarCoverMap_smooth.continuous_fderiv (by simp)).continuousOn
  have hdiff (y : Cover) (hy : y ∈ scalarCoverStrip) :
      HasFDerivAt (H ∘ scalarCoverMap) (scalarCoverPotentialDifferential J y) y := by
    have hHy := (contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
      (scalarAnnulus_isOpen.mem_nhds (scalarCoverMap_mem hy))
    have h := (hHy.differentiableAt (by simp)).hasFDerivAt.comp y
      (scalarCoverMap_smooth.differentiable (by simp) y).hasFDerivAt
    simpa only [scalarCoverPotentialDifferential, hJeq (scalarCoverMap_mem hy)] using h
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hdiff y hy).differentiableAt.differentiableWithinAt)
    scalarCoverStrip_convex scalarCoverStrip_isOpen
    (fun _ _ => (hHc.comp scalarCoverMap_smooth.continuous).continuousWithinAt)
  apply ((hBc z hz).mono subset_closure).tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hdiff y hy).fderiv.symm

/-- Restricting a genuine closed-strip differential to a horizontal boundary line gives an
ordinary two-sided angular derivative. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-25-cover-potential-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalar_closed_strip_hasDerivAt_angle
    {W : Cover → ℝ} {B : Cover → Cover →L[ℝ] ℝ}
    (hdW : ∀ z ∈ closure scalarCoverStrip,
      HasFDerivWithinAt W (B z) (closure scalarCoverStrip) z)
    {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => W (r, s)) (B (r, t) (0, 1)) t := by
  have hline (s : ℝ) : (r, s) ∈ closure scalarCoverStrip := by
    rw [scalarCoverStrip_closure]
    exact hr
  exact (hdW (r, t) (hline t)).comp_hasDerivAt t
    ((hasDerivAt_const t r).prodMk (hasDerivAt_id t)) (Eventually.of_forall hline)

/-- The actual potential differential annihilates the literal angular column on either
boundary circle. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in
`proof-work/tasks/M64/derivations/2026-09-25-cover-potential-boundary-regularity.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarCoverPotential_boundary_angular_zero
    {H : Plane → ℝ} {J : Plane → Plane →L[ℝ] ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hJc : ContinuousOn J (closure scalarAnnulus))
    (hJeq : EqOn J (fderiv ℝ H) scalarAnnulus)
    {r : ℝ} (hr : r = 1 ∨ r = 2) (t : ℝ) :
    scalarCoverPotentialDifferential J (r, t) (0, 1) = 0 := by
  have hd := scalar_closed_strip_hasDerivAt_angle
    (fun z hz => scalarCoverPotential_hasFDerivWithinAt_closure hHc hHs hJc hJeq hz)
    (r := r) (by rcases hr with rfl | rfl <;> norm_num) t
  rcases hr with rfl | rfl
  · have heq : (fun s : ℝ => H (scalarCoverMap (1, s))) = fun _ => 0 := by
      funext s
      apply hinner
      simp only [scalarCoverMap, scalarCirclePoint_norm, abs_one]
    change HasDerivAt (fun s : ℝ => H (scalarCoverMap (1, s))) _ t at hd
    rw [heq] at hd
    exact hd.unique (hasDerivAt_const t 0)
  · have heq : (fun s : ℝ => H (scalarCoverMap (2, s))) = fun _ => 1 := by
      funext s
      apply houter
      norm_num [scalarCoverMap, scalarCirclePoint_norm]
    change HasDerivAt (fun s : ℝ => H (scalarCoverMap (2, s))) _ t at hd
    rw [heq] at hd
    exact hd.unique (hasDerivAt_const t 1)

end PoincareMT.M64Uniformization
