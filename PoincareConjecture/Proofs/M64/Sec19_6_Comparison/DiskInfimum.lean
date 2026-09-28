import PoincareConjecture.Statements.M64Annulus
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Infimum

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}
  {gamma0 gamma1 : C1FreeLoopSpace (M := M)}

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

end PoincareConjecture
