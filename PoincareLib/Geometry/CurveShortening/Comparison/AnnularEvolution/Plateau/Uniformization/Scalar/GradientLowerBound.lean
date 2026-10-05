import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.DifferentialBounds

/-!
# Positive uniform metric-gradient energy

Metric duality transports the constructed continuous covector extension
to a continuous vector field on the closed annulus. Its positive metric
energy has a positive compact minimum, bounding the actual interior
gradient energy away from zero.

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

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- The retained gradient energy is uniformly positive up to the boundary, using the actual
continuous differential extension. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-cover-uniform-differential-bounds.md`. -/
theorem annular_harmonic_gradient_energy_lower_bound
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hnon : ∀ x ∈ scalarAnnulus, fderiv ℝ H x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ scalarAnnulus,
      c ≤ g.inner x (D.gradient H x) (D.gradient H x) := by
  obtain ⟨J, hJc, hJeq, hJn⟩ :=
    annular_harmonic_differential_extension D hHc hHs hlap hinner houter
  have hclosed : closure scalarAnnulus ⊆ {x : Plane | 0 ≤ scalarAnnulusDefining x} :=
    closure_minimal (fun x hx => ((scalarAnnulusDefining_pos x).mpr hx).le)
      (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  have hK : IsCompact (closure scalarAnnulus) :=
    scalarClosedAnnulus_isCompact.of_isClosed_subset isClosed_closure hclosed
  have hKne : (closure scalarAnnulus).Nonempty :=
    scalarAnnulus_isConnected.nonempty.mono subset_closure
  have hinv (x : Plane) : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hIc : Continuous (fun x : Plane => (g.euclideanCoefficients x).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hinv x).contDiffAt_map_inverse.comp x
      (g.contDiffAt_euclideanCoefficients x)).continuousAt
  let Z : Plane → Plane := fun x => (g.euclideanCoefficients x).inverse (J x)
  have hZc : ContinuousOn Z (closure scalarAnnulus) := hIc.continuousOn.clm_apply hJc
  let E : Plane → ℝ := fun x => g.euclideanCoefficients x (Z x) (Z x)
  have hBc : Continuous g.euclideanCoefficients := continuous_iff_continuousAt.mpr
    (fun x => (g.contDiffAt_euclideanCoefficients x).continuousAt)
  have hEc : ContinuousOn E (closure scalarAnnulus) :=
    (hBc.continuousOn.clm_apply hZc).clm_apply hZc
  have hEp (x : Plane) (hx : x ∈ closure scalarAnnulus) : 0 < E x := by
    have hJne : J x ≠ 0 := by
      by_cases hxA : x ∈ scalarAnnulus
      · rw [hJeq hxA]
        exact hnon x hxA
      · exact hJn x hx hxA
    have hZne : Z x ≠ 0 := by
      intro hz
      have h := (hinv x).self_apply_inverse (J x)
      change g.euclideanCoefficients x (Z x) = J x at h
      rw [hz, map_zero] at h
      exact hJne h.symm
    exact g.pos x (Z x) hZne
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne hEc
  refine ⟨E a, hEp a ha, ?_⟩
  intro x hx
  have hgrad : D.gradient H x = Z x := by
    change (g.euclideanCoefficients x).inverse (mvfderiv (𝓡 2) H x) =
      (g.euclideanCoefficients x).inverse (J x)
    rw [hJeq hx]
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  rw [hgrad]
  exact hmin (subset_closure hx)

end PoincareMT.M64Uniformization
