import PoincareConjecture.Definitions.Ch01.Curvature
import PoincareConjecture.Proofs.M04.ConnectionScalar
import PoincareConjecture.Proofs.M04.MetricPairings





set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiffOn_curvatureOnFields (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (D.curvatureOnFields X Y Z)) U := by
  let A := fun y ↦ D.connection Z y (Y y)
  let B := fun y ↦ D.connection Z y (X y)
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g A
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    have hx' : x ∈ U ∩ t.baseSet := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      (hY.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hx')
  have hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% B) U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g B
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    have hx' : x ∈ U ∩ t.baseSet := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      (hX.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hx')
  have hbr : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (VectorField.mlieBracket (𝓡 n) X Y)) U := by
    intro x hx
    have hX' := (hX x hx).contMDiffAt (hU.mem_nhds hx)
    have hY' := (hY x hx).contMDiffAt (hU.mem_nhds hx)
    let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
      apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
      simpa [minSmoothness_eq_infty] using
        (minSmoothness_monotone (𝕜 := ℝ)
          (by
            exact WithTop.coe_le_coe.mpr
              (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
    let : IsManifold (𝓡 n) (∞ + 1) M := by
      simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
    exact (hX'.mlieBracket_vectorField (m := ⊤) (n := ⊤) hY' (by simp)).contMDiffWithinAt
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_section_of_metric_pairings g (D.curvatureOnFields X Y Z)
  intro v
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hx' : x ∈ U ∩ t.baseSet := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hW := (contMDiffOn_extend_baseSet v).mono (Set.inter_subset_right (s := U))
  have h1 := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
    (hX.mono Set.inter_subset_left) (hA.mono Set.inter_subset_left) hW
  have h2 := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
    (hY.mono Set.inter_subset_left) (hB.mono Set.inter_subset_left) hW
  have h3 := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
    (hbr.mono Set.inter_subset_left) (hZ.mono Set.inter_subset_left) hW
  have hs := ((h1.sub h2).sub h3).contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hx')
  simpa only [LeviCivitaData.curvatureOnFields, A, B, map_sub,
    sub_apply] using hs

end PoincareConjecture.M04
