import PoincareLib.Geometry.CurveShortening.Comparison.AnnulusTheory
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Infimum

/-!
# Filling-infimum arithmetic for the two gluing directions

The geometric collar construction supplies both directions with an arbitrary
positive slack.  This file records the separate order-theoretic passage from
those witnesses to the absolute filling-area bound.  The two nonemptiness
hypotheses are kept explicit because `fillingArea` is a totalized infimum.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}
  {gamma0 gamma1 : C1FreeLoopSpace (M := M)}

/-! A forward gluing estimate, with arbitrary positive slack, controls the
first filling infimum. -/
/-- A quantified forward disk-gluing estimate bounds the upper filling infimum using a
genuine near-minimizer. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual
half-disk collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64FillingArea_le_add_of_forward
    {q : ℝ}
    (hD0 : Nonempty (LipschitzSpanningDisk g gamma0))
    (hforward : ∀ eta : ℝ, 0 < eta →
      ∀ D0 : LipschitzSpanningDisk g gamma0,
        ∃ D1 : LipschitzSpanningDisk g gamma1,
          D1.area ≤ D0.area + q + eta) :
    fillingArea g gamma1 ≤ fillingArea g gamma0 + q := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨D0⟩ := hD0
  obtain ⟨Dnear, hnear⟩ := m60FillingArea_near_minimizer_of_disk g gamma0 D0
    (half_pos hepsilon)
  obtain ⟨D1, hglue⟩ := hforward (epsilon / 2) (half_pos hepsilon) Dnear
  have hle := m60FillingArea_le_disk g gamma1 D1
  have hq' : D1.area < fillingArea g gamma0 + q + epsilon := by
    calc
      D1.area ≤ Dnear.area + q + epsilon / 2 := hglue
      _ < (fillingArea g gamma0 + epsilon / 2) + q + epsilon / 2 := by
        linarith
      _ = fillingArea g gamma0 + q + epsilon := by ring
  have hq : D1.area ≤ fillingArea g gamma0 + q + epsilon := hq'.le
  linarith

/-! The reverse direction is the same estimate with the boundary labels
exchanged. -/
/-- The reverse gluing estimate gives the opposite guarded filling-infimum inequality.
Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64FillingArea_le_add_of_reverse
    {q : ℝ}
    (hD1 : Nonempty (LipschitzSpanningDisk g gamma1))
    (hreverse : ∀ eta : ℝ, 0 < eta →
      ∀ D1 : LipschitzSpanningDisk g gamma1,
        ∃ D0 : LipschitzSpanningDisk g gamma0,
          D0.area ≤ D1.area + q + eta) :
    fillingArea g gamma0 ≤ fillingArea g gamma1 + q := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨D1⟩ := hD1
  obtain ⟨Dnear, hnear⟩ := m60FillingArea_near_minimizer_of_disk g gamma1 D1
    (half_pos hepsilon)
  obtain ⟨D0, hglue⟩ := hreverse (epsilon / 2) (half_pos hepsilon) Dnear
  have hle := m60FillingArea_le_disk g gamma0 D0
  have hq' : D0.area < fillingArea g gamma1 + q + epsilon := by
    calc
      D0.area ≤ Dnear.area + q + epsilon / 2 := hglue
      _ < (fillingArea g gamma1 + epsilon / 2) + q + epsilon / 2 := by
        linarith
      _ = fillingArea g gamma1 + q + epsilon := by ring
  have hq : D0.area ≤ fillingArea g gamma1 + q + epsilon := hq'.le
  linarith

/-! The guarded infimum comparison used by `M64DiskGluingConclusion`. -/
/-- Both actual disk-gluing estimates bound the absolute difference of filling areas by the
collar area. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar
in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64FillingArea_abs_sub_le_of_gluing
    {q : ℝ}
    (hD0 : Nonempty (LipschitzSpanningDisk g gamma0))
    (hD1 : Nonempty (LipschitzSpanningDisk g gamma1))
    (hforward : ∀ eta : ℝ, 0 < eta →
      ∀ D0 : LipschitzSpanningDisk g gamma0,
        ∃ D1 : LipschitzSpanningDisk g gamma1,
          D1.area ≤ D0.area + q + eta)
    (hreverse : ∀ eta : ℝ, 0 < eta →
      ∀ D1 : LipschitzSpanningDisk g gamma1,
        ∃ D0 : LipschitzSpanningDisk g gamma0,
          D0.area ≤ D1.area + q + eta) :
    |fillingArea g gamma1 - fillingArea g gamma0| ≤ q := by
  have h01 := m64FillingArea_le_add_of_forward hD0 hforward
  have h10 := m64FillingArea_le_add_of_reverse hD1 hreverse
  rw [abs_le]
  constructor <;> linarith

end PoincareMT
