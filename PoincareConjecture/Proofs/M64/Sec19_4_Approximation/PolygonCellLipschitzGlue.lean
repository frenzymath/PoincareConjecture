import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellLipschitz
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

theorem m64_lipschitzOn_annulus_of_polygon_cells
    {Y : Type*} [PseudoEMetricSpace Y] {f : LoopPlane → Y}
    {N : ℕ} (hN : 0 < N)
    (hcell : ∀ j : Fin N, ∃ K : ℝ≥0,
      LipschitzOnWith K f (m64PolygonCellSet j)) :
    ∃ K : ℝ≥0, LipschitzOnWith K f m64AnnulusDomain := by
  classical
  let S : ℕ → Set LoopPlane := fun k =>
    {p | 0 ≤ p 0 ∧ p 0 ≤ (k : ℝ) * m63CellLength N ∧
      0 ≤ p 1 ∧ p 1 ≤ 1}
  have hell : 0 ≤ m63CellLength N := (m63CellLength_pos hN).le
  have hconvex (k : ℕ) : Convex ℝ (S k) := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ (a • x + b • y) 0 ∧
      (a • x + b • y) 0 ≤ (k : ℝ) * m63CellLength N ∧
      0 ≤ (a • x + b • y) 1 ∧ (a • x + b • y) 1 ≤ 1
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_,
      add_nonneg (mul_nonneg ha hx.2.2.1) (mul_nonneg hb hy.2.2.1), ?_⟩
    · calc
        a * x 0 + b * y 0 ≤ a * ((k : ℝ) * m63CellLength N) +
            b * ((k : ℝ) * m63CellLength N) :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
            (mul_le_mul_of_nonneg_left hy.2.1 hb)
        _ = (k : ℝ) * m63CellLength N := by rw [← add_mul, hab, one_mul]
    · calc
        a * x 1 + b * y 1 ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2.2.2 ha)
            (mul_le_mul_of_nonneg_left hy.2.2.2 hb)
        _ = 1 := by rw [← add_mul, hab, one_mul]
  have hprefix : ∀ k : ℕ, k ≤ N → ∃ K : ℝ≥0, LipschitzOnWith K f (S k) := by
    intro k
    induction k with
    | zero =>
        intro _
        obtain ⟨K, hK⟩ := hcell ⟨0, hN⟩
        refine ⟨K, hK.mono ?_⟩
        intro p hp
        simp only [S, mem_ofPred_eq, Nat.cast_zero, zero_mul] at hp
        change m63CellLeft N ⟨0, hN⟩ ≤ p 0 ∧
          p 0 ≤ m63CellLeft N ⟨0, hN⟩ + m63CellLength N ∧
          0 ≤ p 1 ∧ p 1 ≤ 1
        simp only [m63CellLeft, Nat.cast_zero, zero_mul, zero_add] at hp ⊢
        exact ⟨hp.1, hp.2.1.trans hell, hp.2.2⟩
    | succ k ih =>
        intro hk
        obtain ⟨K, hK⟩ := ih (by omega)
        let j : Fin N := ⟨k, by omega⟩
        obtain ⟨L, hL⟩ := hcell j
        have hleft : S (k + 1) ∩ {p | p 0 ≤ (k : ℝ) * m63CellLength N} ⊆ S k := by
          intro p hp
          exact ⟨hp.1.1, hp.2, hp.1.2.2⟩
        have hright : S (k + 1) ∩ {p | (k : ℝ) * m63CellLength N ≤ p 0} ⊆
            m64PolygonCellSet j := by
          intro p hp
          change m63CellLeft N j ≤ p 0 ∧
            p 0 ≤ m63CellLeft N j + m63CellLength N ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
          refine ⟨hp.2, ?_, hp.1.2.2⟩
          have h := hp.1.2.1
          simpa only [m63CellLeft, j, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            using h
        have hglue := M60.lipschitzOnWith_piecewise_of_convex (hconvex (k + 1))
          (fun p : LoopPlane => p 0)
          (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousOn
          ((k : ℝ) * m63CellLength N) (hK.mono hleft) (hL.mono hright)
          (fun _ _ _ => rfl)
        refine ⟨max K L, ?_⟩
        simpa only [piecewise_same] using hglue
  obtain ⟨K, hK⟩ := hprefix N le_rfl
  refine ⟨K, ?_⟩
  have hSN : S N = m64AnnulusDomain := by
    ext p
    change (0 ≤ p 0 ∧ p 0 ≤ (N : ℝ) * m63CellLength N ∧
      0 ≤ p 1 ∧ p 1 ≤ 1) ↔
      (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1)
    rw [m63_count_mul_cellLength hN]
    rfl
  rwa [hSN] at hK

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64Annulus_hLip_of_polygon_cells
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    {N : ℕ} (hN : 0 < N)
    (hcell : ∀ j : Fin N, ∃ K : ℝ≥0,
      ∀ x ∈ m64PolygonCellSet j, ∀ y ∈ m64PolygonCellSet j,
        g.edist (f x) (f y) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ‖x - y‖) :
    ∃ K : ℝ≥0, ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hcell' : ∀ j : Fin N, ∃ K : ℝ≥0,
      LipschitzOnWith K f (m64PolygonCellSet j) := by
    intro j
    obtain ⟨K, hK⟩ := hcell j
    refine ⟨K, ?_⟩
    intro x hx y hy
    change g.edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y
    simpa only [edist_dist, dist_eq_norm] using hK x hx y hy
  obtain ⟨K, hK⟩ := m64_lipschitzOn_annulus_of_polygon_cells hN hcell'
  refine ⟨K, ?_⟩
  intro x y
  have h := hK x.property y.property
  change g.edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist (x : LoopPlane) y at h
  simpa only [edist_dist, dist_eq_norm] using h

end PoincareConjecture
