import PoincareConjecture.Proofs.M58.Cor18_28_AreaBound
import PoincareConjecture.Proofs.M58.Cor18_28_UniformBounds
import PoincareConjecture.Proofs.M58.Cor18_28_Fillings

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem exists_short_disk_linear_area_bound (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ γ : C1FreeLoopSpace (M := M), freeLoopLength g γ < ρ →
        ∃ D : LipschitzSpanningDisk g γ, D.area ≤ K * freeLoopLength g γ := by
  obtain ⟨C, U, A, B, hU, hdiag, hA, hB, h0, h1, hC, ht, hq⟩ :=
    exists_bounded_local_contraction g hcompact
  obtain ⟨ρ, hρ, hshort⟩ := exists_short_loop_diagonal_radius g hcompact hU
    (fun p => hdiag (by rfl : (p, p) ∈ diagonal M))
  obtain ⟨H, hH, hprofile⟩ := exists_diskTimeProfile_derivative_bound
  refine ⟨ρ, H * A * B, hρ, mul_nonneg (mul_nonneg hH hA) hB, ?_⟩
  intro γ hγ
  let p := γ loopCircleBasepoint
  have hpair (z : LoopCircle) : (p, γ z) ∈ U := hshort γ hγ z
  have hangle (t : ℝ) : (p, periodicFreeLoop γ t) ∈ U := by
    have heq : periodicFreeLoop γ t = γ ⟨angularPoint t, norm_angularPoint t⟩ :=
      γ.boundary ⟨angularPoint t, norm_angularPoint t⟩
    rw [heq]
    exact hpair _
  have hF : ContMDiff (𝓡 2) (𝓡 3) 1 (contractionDiskMap C p γ) :=
    contMDiff_contractionDiskMap C p γ (fun z => h1 _ (hpair z))
      (fun t z => hC _ ⟨t.property, hpair z⟩)
  refine ⟨spanningDiskOfC1 g γ (contractionDiskMap C p γ) hF
    (contractionDiskMap_boundary C h0 p γ), ?_⟩
  rw [spanningDiskOfC1_area]
  exact contractionDiskMap_area_le g C p γ hF
    (fun s hs t => hC _ ⟨hs, hangle t⟩) hA hH
    (fun s hs t => ht _ ⟨hs, hangle t⟩)
    (fun s hs t => hq _ ⟨hs, hangle t⟩) hprofile

theorem small_loop_filling (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) (η : ℝ) (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < η / 2 ∧
      ∀ γ : C1FreeLoopSpace (M := M), freeLoopLength g γ < ζ →
        ∃ D : LipschitzSpanningDisk g γ, D.area < η := by
  obtain ⟨ρ, K, hρ, hK, hfill⟩ := exists_short_disk_linear_area_bound g hcompact
  have hK1 : 0 < K + 1 := by linarith
  let ζ := min ρ (min (η / 4) (η / (K + 1)))
  have hζ : 0 < ζ := lt_min hρ (lt_min (div_pos hη (by norm_num)) (div_pos hη hK1))
  have hζη : ζ < η / 2 :=
    (min_le_right ρ _ |>.trans (min_le_left _ _)).trans_lt (by linarith)
  refine ⟨ζ, hζ, hζη, ?_⟩
  intro γ hγ
  obtain ⟨D, hD⟩ := hfill γ (hγ.trans_le (min_le_left _ _))
  refine ⟨D, ?_⟩
  have hlen : freeLoopLength g γ < η / (K + 1) :=
    hγ.trans_le (min_le_right ρ _ |>.trans (min_le_right _ _))
  have hmul := (lt_div_iff₀ hK1).mp hlen
  have hnonneg := freeLoopLength_nonneg g γ
  nlinarith

end PoincareConjecture.Proofs.M58
