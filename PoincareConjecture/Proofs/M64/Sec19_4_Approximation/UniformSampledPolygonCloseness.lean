import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledPolygonCloseness
import PoincareConjecture.Definitions.M64Approximation
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.RawLoopLength
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m64_compact_family_speed_bound
    (g : RiemannianMetric 3 M)
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ z : Z, ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (periodicFreeLoop (Gamma z) x)
        (curveVelocity (periodicFreeLoop (Gamma z)) x) ≤ S := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let Y := Z × Icc (0 : ℝ) curvePeriod
  have hjet : Continuous (fun w : Y =>
      m63AngularFirstJet (periodicFreeLoop (Gamma w.1)) w.2) :=
    m63AngularFirstJet_continuous.comp
      ((hGamma.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hspeed : Continuous (fun w : Y =>
      g.tangentNorm (periodicFreeLoop (Gamma w.1) w.2)
        (curveVelocity (periodicFreeLoop (Gamma w.1)) w.2)) :=
    (hjet.inner_bundle hjet).sqrt
  obtain ⟨S0, hS0⟩ := (isCompact_range hspeed).bddAbove
  refine ⟨max S0 0, le_max_right _ _, ?_⟩
  intro z x hx
  exact (hS0 (mem_range_self (z, (⟨x, hx⟩ : Icc (0 : ℝ) curvePeriod)))).trans
    (le_max_left _ _)

theorem m64_exists_mesh_threshold {S r : ℝ} (hr : 0 < r) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      2 * S * m63CellLength N < r := by
  obtain ⟨N0, hlarge⟩ := exists_nat_gt
    (max (1 : ℝ) (2 * S * curvePeriod / r))
  have hN0 : 0 < N0 := by
    have h1 : (1 : ℝ) < N0 := (le_max_left _ _).trans_lt hlarge
    exact_mod_cast (zero_lt_one.trans h1)
  refine ⟨N0, hN0, ?_⟩
  intro N hN0N
  have hN : 0 < N := hN0.trans_le hN0N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : 2 * S * curvePeriod / r < (N : ℝ) :=
    ((le_max_right _ _).trans_lt hlarge).trans_le (by exact_mod_cast hN0N)
  have hprod := (div_lt_iff₀ hr).mp hratio
  dsimp only [m63CellLength]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hNreal).mpr
  nlinarith only [hprod]

theorem m64_uniform_sampled_polygon_short
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma)
    {r : ℝ} (hr : 0 < r) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ z : Z,
      ∀ polygon : M63GeodesicPolygon g D N,
        M64SampledPolygon (Gamma z) polygon → ∀ x : ℝ,
          g.edist (periodicFreeLoop (Gamma z) x) (polygon.map x) <
            ENNReal.ofReal r := by
  obtain ⟨S, hS, hbound⟩ := m64_compact_family_speed_bound g Gamma hGamma
  obtain ⟨N0, hN0, hmesh⟩ := m64_exists_mesh_threshold (S := S) hr
  refine ⟨N0, hN0, ?_⟩
  intro N hN0N z polygon hsampled x
  have hN : 0 < N := hN0.trans_le hN0N
  exact (m64_sampled_polygon_edist_le hN polygon
    (Proofs.M58.contMDiff_periodicFreeLoop (Gamma z))
    (Proofs.M58.periodic_periodicFreeLoop (Gamma z))
    hsampled hS (hbound z) x).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (hmesh N hN0N))

theorem m64_uniform_compact_sampled_polygon_short
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (X : Set (C1FreeLoopSpace (M := M))) (hX : IsCompact X)
    {r : ℝ} (hr : 0 < r) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        ∀ polygon : M63GeodesicPolygon g D N,
          M64SampledPolygon gamma polygon → ∀ x : ℝ,
            g.edist (periodicFreeLoop gamma x) (polygon.map x) <
              ENNReal.ofReal r := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨N0, hN0, hshort⟩ := m64_uniform_sampled_polygon_short g D
    (fun gamma : X => gamma.1) continuous_subtype_val hr
  exact ⟨N0, hN0, fun N hN gamma hgamma polygon hsampled x =>
    hshort N hN ⟨gamma, hgamma⟩ polygon hsampled x⟩

end PoincareConjecture
