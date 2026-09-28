import PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeFlagProjection









set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem exists_embedded_three_finite_triangulation
    {N : Nat} (hN : 3 < N) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p)) :
    ∃ (I : Type) (_ : PartialOrder I) (_ : Fintype I),
      Nonempty ((finiteOrderComplex I).space ≃ₜ M) ∧
        ∀ t ∈ (finiteOrderComplex I).faces, t.card ≤ 4 := by
  classical
  let L : Real := N + 1
  let b : Real := ambientGridGap N (N - 4)
  let eta : Real := b / (4 * L * (2 : Real) ^ (N + 1))
  let C : Real := 96 * L ^ 2 / b * ((1 + eta⁻¹) ^ 4 - 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : 0 < b := by
    dsimp [b, ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hpower : 0 ≤ (1 + eta⁻¹) ^ 4 - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (le_add_of_nonneg_right (inv_nonneg.mpr heta.le)))
  have hC : 0 ≤ C := mul_nonneg (by positivity) hpower
  let eps : Real := min (b / (1000 * L)) (1 / (2 * (C + 1)))
  have heps : 0 < eps := by dsimp [eps]; positivity
  let epsilon : NNReal := ⟨eps, heps.le⟩
  have hepsilon : 0 < epsilon := heps
  have hepsgrid : (epsilon : Real) ≤ ambientGridGap N (N - 4) / (1000 * (N + 1)) :=
    min_le_left _ _
  have hcoefficient :
      96 * (N + 1 : Real) ^ 2 * (epsilon : Real) / ambientGridGap N (N - 4) *
        ((1 + (ambientGridGap N (N - 4) /
          (4 * (N + 1 : Real) * (2 : Real) ^ (N + 1)))⁻¹) ^ 4 - 1) ≤
            ((1 / 2 : NNReal) : Real) := by
    have hepsbound : eps * (2 * (C + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : Real) < 2 * (C + 1))).mp (min_le_right _ _)
    change 96 * L ^ 2 * eps / b * ((1 + eta⁻¹) ^ 4 - 1) ≤ (1 / 2 : Real)
    calc
      96 * L ^ 2 * eps / b * ((1 + eta⁻¹) ^ 4 - 1) = eps * C := by dsimp [C]; ring
      _ ≤ 1 / 2 := by nlinarith
  obtain ⟨r, hr, hc, hnormal⟩ := exists_embedded_three_nearest_neighborhood e hs he hi
  obtain ⟨G, hG⟩ := exists_embedded_three_flag_grid hN e hs he hi epsilon hepsilon
    hepsgrid (r / (10 * L)) (by positivity)
  have hscale : 2 * (N + 1 : Real) * G.h < r := by
    have h := (lt_div_iff₀ (by positivity : (0 : Real) < 10 * L)).mp hG
    have hpos := mul_pos hL G.h_pos
    change 2 * L * G.h < r
    nlinarith
  refine ⟨G.activeFaces, inferInstance, inferInstance,
    ⟨G.flagHomeomorphOfNearest hs r hc hnormal hscale (1 / 2) (by norm_num) hcoefficient⟩,
    G.activeFlag_faces_card_le_four⟩

end PoincareConjecture.Proofs.M02.Topology
