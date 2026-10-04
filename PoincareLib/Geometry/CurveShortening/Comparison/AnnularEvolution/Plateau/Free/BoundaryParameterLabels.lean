import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.PhaseBoundaryLabels

/-!
# Chords in the original raw boundary parameter

The monotone interpolation theorem also applies with the identity phase
coordinate. This constructs the actual original-parameter chord label,
retaining normalization and the complementary values. Source: Lemaire 1982,
p. 102; M64 phase-cone normalization derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareMT.M64FreeWeakPhaseAnnulus

/-- The actual lower label may be replaced by its affine parameter chord, with the same
period, normalization and complementary trace. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449; M64 derivation 2026-09-26-phase-cone-normalization.md. -/
theorem exists_lower_parameter_chord_label {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : M → EuclideanSpace ℝ (Fin m)}
    {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
    {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < curvePeriod) :
    ∃ sigma : ℝ → ℝ, Continuous sigma ∧ Monotone sigma ∧
      (∀ x, sigma (x + curvePeriod) = sigma x + curvePeriod) ∧
      sigma 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ x ∈ Icc a b, sigma x =
        AffineMap.lineMap (A.label0 a) (A.label0 b) ((x - a) / (b - a))) ∧
      EqOn sigma A.label0 (Icc 0 curvePeriod \ Icc a b) := by
  obtain ⟨sigma, hc, hm, hp, hzero, hchord, houtside⟩ :=
    m64Monotone_phase_chord_replacement (by unfold curvePeriod; positivity)
      ha hab hb (OrderIso.refl ℝ) (fun _ => rfl) A.label0
      (A.labels_continuous hH0 hH1).1 A.label0_monotone A.label0_period
  exact ⟨sigma, hc, hm, hp, hzero.symm ▸ A.label0_normalized, hchord, houtside⟩

end PoincareMT.M64FreeWeakPhaseAnnulus
