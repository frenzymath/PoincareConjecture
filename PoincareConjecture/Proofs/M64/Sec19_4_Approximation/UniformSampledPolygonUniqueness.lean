import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSideUniqueness
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonCloseness
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledPolygonSpeed
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonMapUniqueness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m64_uniform_sampled_polygon_unique
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ z : Z,
      ∀ polygon other : M63GeodesicPolygon g D N,
        M64SampledPolygon (Gamma z) polygon →
        M64SampledPolygon (Gamma z) other →
        ∀ x : ℝ, other.map x = polygon.map x := by
  obtain ⟨r, hr, huniq⟩ := m64_exists_uniform_minimizing_side_uniqueness g hcompact
  obtain ⟨S, hS, hbound⟩ := m64_compact_family_speed_bound g Gamma hGamma
  obtain ⟨N0, hN0, hmesh⟩ := m64_exists_mesh_threshold (S := S) hr
  refine ⟨N0, hN0, ?_⟩
  intro N hN0N z polygon other hsampled hother
  have hN : 0 < N := hN0.trans_le hN0N
  have hell : 0 < m63CellLength N := m63CellLength_pos hN
  have hspeed := m64_sampled_polygon_side_speed_le hN polygon
    (Proofs.M58.contMDiff_periodicFreeLoop (Gamma z))
    (Proofs.M58.periodic_periodicFreeLoop (Gamma z)) hsampled hS (hbound z)
  have hcompare {p q p' q' : M} (hp : p' = p) (hq : q' = q)
      (hpq : g.edist p q < ENNReal.ofReal r)
      (side : M63MinimizingGeodesicSide g D (m63CellLength N) p q)
      (side' : M63MinimizingGeodesicSide g D (m63CellLength N) p' q') :
      EqOn side'.map side.map (Icc (0 : ℝ) (m63CellLength N)) := by
    subst p'
    subst q'
    exact huniq hell hpq side side'
  apply m64_polygon_map_eq_of_side_map_eq polygon other hN
  intro j s hs
  have hpq : g.edist (polygon.vertices j) (polygon.vertices (finRotate N j)) <
      ENNReal.ofReal r := by
    rw [(polygon.side j).edist_eq_length hell.le]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    calc
      m63CellLength N * (polygon.side j).speed ≤ m63CellLength N * S :=
        mul_le_mul_of_nonneg_left (hspeed j) hell.le
      _ ≤ 2 * S * m63CellLength N := by nlinarith [mul_nonneg hS hell.le]
      _ < r := hmesh N hN0N
  exact hcompare ((hother j).trans (hsampled j).symm)
    ((hother (finRotate N j)).trans (hsampled (finRotate N j)).symm)
    hpq (polygon.side j) (other.side j) hs

theorem m64_uniform_compact_sampled_polygon_unique
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    (X : Set (C1FreeLoopSpace (M := M))) (hX : IsCompact X) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        ∀ polygon other : M63GeodesicPolygon g D N,
          M64SampledPolygon gamma polygon → M64SampledPolygon gamma other →
          ∀ x : ℝ, other.map x = polygon.map x := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨N0, hN0, huniq⟩ := m64_uniform_sampled_polygon_unique g D hcompact
    (fun gamma : X => gamma.1) continuous_subtype_val
  exact ⟨N0, hN0, fun N hN gamma hgamma polygon other hsampled hother =>
    huniq N hN ⟨gamma, hgamma⟩ polygon other hsampled hother⟩

end PoincareConjecture
