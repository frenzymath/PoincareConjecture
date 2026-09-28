import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorHorizontalColumn
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonCloseness
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellEventually














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]





theorem m64_sampled_interpolator_horizontal_column_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {r S B : ℝ} (hr : 0 < r) (hS : 0 ≤ S)
    (H : ℝ × (M × M) → M)
    (hH : ContMDiffOn
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ
        {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p q : M,
      g.edist p q ≤ ENNReal.ofReal (r / 2) →
      ∀ v : TangentSpace (𝓡 3) p, g.tangentNorm p v ≤ S →
      ∀ w : TangentSpace (𝓡 3) q, g.tangentNorm q w ≤ S →
        g.tangentNorm (H (t, p, q))
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) H
            (t, p, q) (0, v, w)) ≤ B)
    {N : ℕ} (hN : 0 < N) (gamma : C1FreeLoopSpace (M := M))
    (polygon : M63GeodesicPolygon g D N)
    (hsampled : M64SampledPolygon gamma polygon)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (periodicFreeLoop gamma x)
        (curveVelocity (periodicFreeLoop gamma) x) ≤ S)
    (hshort : ∀ x : ℝ,
      g.edist (periodicFreeLoop gamma x) (polygon.map x) < ENNReal.ofReal (r / 2)) :
    ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (H (z 1, periodicFreeLoop gamma (z 0), polygon.map (z 0)))
        (mfderiv (𝓡 2) (𝓡 3)
          (fun p : LoopPlane => H (p 1, periodicFreeLoop gamma (p 0),
            polygon.map (p 0))) z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B := by
  have hU : IsOpen {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} := by
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    exact isOpen_lt continuous_edist continuous_const
  have hsideBound := m64_sampled_polygon_side_speed_le hN polygon
    (Proofs.M58.contMDiff_periodicFreeLoop gamma)
    (Proofs.M58.periodic_periodicFreeLoop gamma) hsampled hS hbound
  filter_upwards [m64_polygon_cells_interior_ae hN] with z hz
  obtain ⟨j, hzj⟩ := hz
  have hcell : z ∈ m64PolygonCellSet j := interior_subset hzj
  have hdom := m64PolygonCellSet_subset_annulusDomain hN j hcell
  have htime : z 1 ∈ Icc (0 : ℝ) 1 := ⟨hdom.2.2.1, hdom.2.2.2⟩
  have htime' : z 1 ∈ Ioo (-1 : ℝ) 2 := by
    constructor <;> linarith [htime.1, htime.2]
  have hs : z 0 - m63CellLeft N j ∈ Icc (0 : ℝ) (m63CellLength N) := by
    constructor <;> linarith [hcell.1, hcell.2.1]
  have hpoly : polygon.map (z 0) =
      (polygon.side j).map (z 0 - m63CellLeft N j) :=
    (m64_polygon_map_eventuallyEq_side_of_cell_interior polygon j hzj).self_of_nhds
  have hshortSide : g.edist (periodicFreeLoop gamma (z 0))
      ((polygon.side j).map (z 0 - m63CellLeft N j)) < ENNReal.ofReal (r / 2) := by
    rw [← hpoly]
    exact hshort (z 0)
  have hpq : g.edist (periodicFreeLoop gamma (z 0))
      ((polygon.side j).map (z 0 - m63CellLeft N j)) < ENNReal.ofReal r :=
    hshortSide.trans ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  let beta : ℝ → M := fun x => (polygon.side j).map (x - m63CellLeft N j)
  have hgammaAt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
      (periodicFreeLoop gamma) (z 0) :=
    (Proofs.M58.contMDiff_periodicFreeLoop gamma (z 0)).mdifferentiableAt one_ne_zero
  have hsideAt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
      (polygon.side j).map (z 0 - m63CellLeft N j) :=
    ((polygon.side j).smooth.contMDiffAt
      ((polygon.side j).domain_open.mem_nhds
        ((polygon.side j).interval_subset hs))).mdifferentiableAt (by simp)
  have hbetaAt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) beta (z 0) :=
    hsideAt.comp (z 0) ((hasDerivAt_id (z 0)).sub_const
      (m63CellLeft N j)).differentiableAt.mdifferentiableAt
  have hHat : MDifferentiableAt
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) H
        (z 1, periodicFreeLoop gamma (z 0), beta (z 0)) := by
    have hmem : (z 1, periodicFreeLoop gamma (z 0), beta (z 0)) ∈
        Ioo (-1 : ℝ) 2 ×ˢ {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} :=
      ⟨htime', hpq⟩
    exact (hH.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds hmem)).mdifferentiableAt
      (by simp)
  have hbetaBound : g.tangentNorm (beta (z 0)) (curveVelocity beta (z 0)) ≤ S := by
    change g.tangentNorm ((polygon.side j).map (z 0 - m63CellLeft N j))
      (curveVelocity (fun x => (polygon.side j).map (x - m63CellLeft N j)) (z 0)) ≤ S
    rw [m64_translated_side_speed (polygon.side j) hs]
    exact hsideBound j
  have hevent := m64_interpolator_map_eventuallyEq_cell_extension
    (gamma := periodicFreeLoop gamma) (H := H) polygon j hzj
  have hvalue := hevent.self_of_nhds
  change H (z 1, periodicFreeLoop gamma (z 0), polygon.map (z 0)) =
    H (z 1, periodicFreeLoop gamma (z 0), beta (z 0)) at hvalue
  have hderiv := hevent.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 3)
  rw [hvalue, hderiv]
  rw [m64_interpolator_horizontal_column_eq z hgammaAt hbetaAt hHat]
  exact hB (z 1) htime (periodicFreeLoop gamma (z 0)) (beta (z 0))
    hshortSide.le (curveVelocity (periodicFreeLoop gamma) (z 0))
    (hbound (z 0) ⟨hdom.1, hdom.2.1⟩) (curveVelocity beta (z 0)) hbetaBound




theorem m64_uniform_interpolator_horizontal_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    {r : ℝ} (hr : 0 < r) (H : ℝ × (M × M) → M)
    (hH : ContMDiffOn
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ
        {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}))
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ z : Z,
        ∀ polygon : M63GeodesicPolygon g D N,
          M64SampledPolygon (Gamma z) polygon →
          (∀ x : ℝ, g.edist (periodicFreeLoop (Gamma z) x) (polygon.map x) <
            ENNReal.ofReal (r / 2)) ∧
          ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
            g.tangentNorm
              (H (p 1, periodicFreeLoop (Gamma z) (p 0), polygon.map (p 0)))
              (mfderiv (𝓡 2) (𝓡 3)
                (fun q : LoopPlane => H (q 1, periodicFreeLoop (Gamma z) (q 0),
                  polygon.map (q 0))) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B := by
  obtain ⟨S, hS, hspeed⟩ := m64_compact_family_speed_bound g Gamma hGamma
  obtain ⟨B, hB, hbound⟩ :=
    m64_interpolator_endpoint_bound_on_short_tube g hcompact hr H hH S
  obtain ⟨N0, hN0, hmesh⟩ := m64_exists_mesh_threshold (S := S) (half_pos hr)
  refine ⟨B, hB, N0, hN0, ?_⟩
  intro N hN0N z polygon hsampled
  have hN : 0 < N := hN0.trans_le hN0N
  have hshort : ∀ x : ℝ,
      g.edist (periodicFreeLoop (Gamma z) x) (polygon.map x) <
        ENNReal.ofReal (r / 2) := by
    intro x
    exact (m64_sampled_polygon_edist_le hN polygon
      (Proofs.M58.contMDiff_periodicFreeLoop (Gamma z))
      (Proofs.M58.periodic_periodicFreeLoop (Gamma z))
      hsampled hS (hspeed z) x).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (half_pos hr)).mpr (hmesh N hN0N))
  exact ⟨hshort, m64_sampled_interpolator_horizontal_column_bound
    g D hr hS H hH hbound hN (Gamma z) polygon hsampled (hspeed z) hshort⟩

end PoincareConjecture
