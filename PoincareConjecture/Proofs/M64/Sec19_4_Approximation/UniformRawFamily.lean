import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSmoothSampledFamily
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.StaticFlattenedLength
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonAnnuli
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.RawBoundaryReparam
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonChordLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.UniformFillingAreaComparison
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CloseLoopFamilyHomotopy
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.UniformSampledChordLength












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture





theorem m64_uniform_raw_family
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily Gamma) {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∃ A : M64RawFamilyApproximation g D Gamma zeta, A.count = N := by
  classical
  let sphereEquiv : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  let : CompactSpace LoopTwoSphere := sphereEquiv.compactSpace
  obtain ⟨_hbounded, _hattained, hL, hlength⟩ := m63FamilyLengthSup_properties g Gamma
  obtain ⟨NC, hNC, hchord⟩ :=
    M63.exists_uniform_sampled_chord_length g hcompact Gamma hzeta
  obtain ⟨deltaH, hdeltaH, hhom⟩ :=
    M63.exists_uniform_close_loop_family_homotopy (Z := LoopTwoSphere) g hcompact
  obtain ⟨deltaA, hdeltaA, harea⟩ :=
    m63_exists_uniform_filling_area_comparison g hcompact
      (Lambda := 2 * m63FamilyLengthSup g Gamma) (mul_nonneg (by norm_num) hL) hzeta
  obtain ⟨NS, hNS, hsmooth⟩ := m64_exists_uniform_sampled_smooth_loop_family
    g D hcompact Gamma (lt_min hdeltaH hdeltaA)
  obtain ⟨NA, hNA, hannuli⟩ := m64_uniform_sampled_polygon_annuli
    g D hcompact Gamma Gamma.continuous hzeta
  refine ⟨max NC (max NS NA), hNC.trans_le (le_max_left _ _), ?_⟩
  intro N hN0N
  have hNCN : NC ≤ N := (le_max_left _ _).trans hN0N
  have hNSN : NS ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN0N)
  have hNAN : NA ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN0N)
  have hN : 0 < N := hNC.trans_le hNCN
  obtain ⟨polygon, hsample, family, hangular, hsmoothFamily, hfirst, hsecond, hclose⟩ :=
    hsmooth N hNSN
  have hcloseH (z : LoopTwoSphere) (x : LoopCircle) :
      g.edist (family z x) (Gamma z x) < ENNReal.ofReal deltaH :=
    (hclose z x).trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hcloseA (z : LoopTwoSphere) (x : LoopCircle) :
      g.edist (family z x) (Gamma z x) < ENNReal.ofReal deltaA :=
    (hclose z x).trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hflatLength (z : LoopTwoSphere) :
      freeLoopLength g (family z) = m64PolygonLength (polygon z) :=
    m64_freeLoopLength_eq_polygonLength hN (polygon z) (family z) (hangular z)
  have hlengthEq (z : LoopTwoSphere) : freeLoopLength g (family z) =
      ∑ j : Fin N, (g.edist
        (periodicFreeLoop (Gamma z) (m63CellLeft N j))
        (periodicFreeLoop (Gamma z) (m63CellLeft N (finRotate N j)))).toReal := by
    rw [hflatLength z]
    exact m64PolygonLength_eq_sampled_chord_sum (polygon z) hN
      (periodicFreeLoop (Gamma z)) (Proofs.M58.periodic_periodicFreeLoop (Gamma z))
      (Proofs.M58.contMDiff_periodicFreeLoop (Gamma z)) (hsample z)
  have hloss (z : LoopTwoSphere) :
      0 ≤ freeLoopLength g (Gamma z) - freeLoopLength g (family z) ∧
      freeLoopLength g (Gamma z) - freeLoopLength g (family z) < zeta := by
    rw [hlengthEq z]
    exact hchord N hNCN z
  obtain ⟨hhomotopic, htransfer⟩ := hhom Gamma family hcloseH
  have hfamilyNull : M61NullFamily family := fun z => htransfer z (hnull z)
  have hareaError (z : LoopTwoSphere) :
      |fillingArea g (family z) - fillingArea g (Gamma z)| < zeta := by
    apply harea (Gamma z) (family z) (hnull z) (hfamilyNull z) (hcloseA z)
    linarith only [hlength z, (hloss z).1]
  let boundary : ∀ z, M64PolygonBoundary (polygon z) :=
    fun z => Classical.choice (exists_polygon_boundary (polygon z))
  let reparam := m64CircleReparamFromFlattening N hN
  have hboundary (z : LoopTwoSphere) (w : LoopCircle) :
      (boundary z).map w = family z (reparam.map w) :=
    m64_polygon_boundary_eq_flattened_family hN (hangular z) w
  have hboundaryCont : Continuous
      (fun p : LoopTwoSphere × LoopCircle => (boundary p.1).map p.2) := by
    have h : Continuous (fun p : LoopTwoSphere × LoopCircle =>
        family p.1 (reparam.map p.2)) :=
      Proofs.M58.continuous_loop_eval.comp
        ((family.continuous.comp continuous_fst).prodMk
          (reparam.continuous_map.comp continuous_snd))
    exact h.congr (fun p => (hboundary p.1 p.2).symm)
  have hangle : Continuous m64LoopCircleParam := by
    change Continuous (fun x : ℝ =>
      (⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ : LoopCircle))
    exact Proofs.M58.contDiff_angularPoint.continuous.subtype_mk _
  have hpolygonCont : Continuous
      (fun p : LoopTwoSphere × ℝ => (polygon p.1).map p.2) :=
    (hboundaryCont.comp (continuous_fst.prodMk (hangle.comp continuous_snd))).congr
      (fun p => (boundary p.1).angular_eq p.2)
  have hsource (z : LoopTwoSphere) : FillingAreaData g (family z) :=
    Classical.choice (m60FillingData_of_null g (family z) (hfamilyNull z))
  let rawDisk : ∀ z : LoopTwoSphere, M64RawSpanningDisk g (boundary z).map :=
    fun z => m64RawDiskOfBoundaryReparam reparam (hboundary z)
      (Classical.choice (hsource z).nonempty)
  choose annulus hpiecewise hgeodesic hnonnegative hsmall using
    fun z => hannuli N hNAN z (polygon z) (hsample z)
  refine ⟨{
    count := N
    count_positive := hN
    polygon := polygon
    sampled := hsample
    boundary := boundary
    polygon_continuous := hpolygonCont
    boundary_continuous := hboundaryCont
    polygon_length := fun z => m64PolygonLength_eq_sum (polygon z) hN
    raw_null := fun z => m64RawNullLoop_of_boundary_reparam
      (hfamilyNull z) reparam (hboundary z)
    source_filling := fun z =>
      Classical.choice (m60FillingData_of_null g (Gamma z) (hnull z))
    raw_disk_nonempty := fun z => ⟨rawDisk z⟩
    raw_area_bounded_below := fun z => m64RawDiskAreaRange_bddBelow (rawDisk z)
    raw_area_nonnegative := fun z => m64RawFillingArea_nonnegative (rawDisk z)
    raw_area_error := ?_
    annulus := annulus
    annulus_piecewise := hpiecewise
    annulus_geodesic := hgeodesic
    annulus_area := fun z => ⟨hnonnegative z, hsmall z⟩
    family := family
    null_family := hfamilyNull
    homotopic := hhomotopic
    angular_eq := hangular
    angular_smooth := hsmoothFamily
    first_jet_continuous := hfirst
    second_jet_continuous := hsecond
    flattened_length := hflatLength
    family_filling := hsource
    flattening_area_range := fun z =>
      m64RawDiskAreaRange_eq_of_boundary_reparam reparam (hboundary z)
    length_loss := hloss
    area_error := hareaError }, rfl⟩
  intro z
  rw [m64RawFillingArea_eq_fillingArea_of_boundary_reparam reparam (hboundary z)]
  exact hareaError z

end PoincareConjecture
