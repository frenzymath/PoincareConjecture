import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedInteriorWall
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckRegionConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem intrinsicEDist_central_sphere_le (N : EpsilonNeck g)
    {U : Set M} (hSU : N.central_sphere ⊆ U) {x y : M}
    (hx : x ∈ N.central_sphere) (hy : y ∈ N.central_sphere) :
    intrinsicEDist g U x y ≤
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) := by
  obtain ⟨gamma, h0, h1, hgamma, hS, hlength, _, _⟩ :=
    exists_central_sphere_shortcut N hx hy
  have hle := intrinsicEDist_le_pathELength g zero_le_one hgamma.contMDiffOn
    (fun t (_ : t ∈ Icc (0 : ℝ) 1) => hSU (hS (mem_univ t)))
  rw [h0, h1] at hle
  exact hle.trans hlength.le

theorem intrinsicOpenMetric_edist_neck_to_sphere_le (N : EpsilonNeck g)
    (U : TopologicalSpace.Opens M) (hNU : N.carrier ⊆ (U : Set M))
    {q y : U} (hq : (q : M) ∈ N.carrier) (hy : (y : M) ∈ N.central_sphere) :
    (intrinsicOpenMetric g U).edist q y ≤ ENNReal.ofReal
      ((2 * N.epsilon⁻¹ + 8 * standardSpherePathCeiling) * N.scale) := by
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let z : U := ⟨N.center, hNU (N.central_sphere_subset N.center_on_central_sphere)⟩
  have hepsilon : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hscale : 0 < N.scale := N.scale_pos
  have hL : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  have hregion : (q : M) ∈ N.region (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨hq, (N.coordinate_inverse_mem q hq).2⟩
  obtain ⟨gamma, h0, h1, hgamma, hN, hlength⟩ :=
    exists_neck_region_center_connector N (neg_neg_of_pos hepsilon) hepsilon hregion
  have hfirst : gU.edist q z ≤ ENNReal.ofReal
      ((2 * N.epsilon⁻¹ + 4 * standardSpherePathCeiling) * N.scale) := by
    have hle := intrinsicEDist_le_pathELength g zero_le_one hgamma
      (fun t ht => hNU (hN ht).1)
    rw [h0, h1, ← intrinsicOpenMetric_edist g U q z] at hle
    exact hle.trans hlength.le
  have hsecond : gU.edist z y ≤
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) := by
    rw [intrinsicOpenMetric_edist]
    exact intrinsicEDist_central_sphere_le N (N.central_sphere_subset.trans hNU)
      N.center_on_central_sphere hy
  calc
    gU.edist q y ≤ gU.edist q z + gU.edist z y := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((2 * N.epsilon⁻¹ + 4 * standardSpherePathCeiling) * N.scale) +
        ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) :=
      add_le_add hfirst hsecond
    _ = ENNReal.ofReal
        ((2 * N.epsilon⁻¹ + 8 * standardSpherePathCeiling) * N.scale) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [T3Space M] {X : Set M}

theorem exists_selected_chain_tail_with_scale_lt
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (D : LeviCivitaData g) (hR : ContinuousOn D.scalarCurvature T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D.scalarCurvature y ≤ 2 * D.scalarCurvature z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x)
    {c sigma : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1) (hsigma : 0 < sigma) :
    ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ i ∈ T.chain.shape.active, ∀ y ∈ (T.chain.neck i).carrier,
        d < (A.inverse y).2 →
          (T.chain.neck i).carrier ⊆ A.tail true c ∧ (T.chain.neck i).scale < sigma := by
  obtain ⟨a, ha, ha1, hhigh⟩ := hdiverge (1 / sigma ^ 2)
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hmax0 : 0 < max c a := lt_max_of_lt_left hc0
  have hmax1 : max c a < 1 := max_lt hc1 ha1
  obtain ⟨d, hd, hd1, hwhole⟩ :=
    exists_selected_chain_tail_above_cylinder_level T A D.scalarCurvature hR hratio
      hdiverge (lt_max_of_lt_left hc) hmax1
  refine ⟨d, hd, hd1, ?_⟩
  intro i hi y hy hdy
  have hN := hwhole i hi y hy hdy
  have hcenter := (A.mem_tail_iff_m28 true hmax0 hmax1).mp
    (hN ((T.chain.neck i).central_sphere_subset (T.chain.neck i).center_on_central_sphere))
  have hRc := hhigh (T.chain.neck i).center hcenter.1
    ((le_max_right _ _).trans_lt hcenter.2)
  have hRcpos : 0 < D.scalarCurvature (T.chain.neck i).center :=
    (one_div_pos.mpr (sq_pos_of_pos hsigma)).trans hRc
  have hprod : 1 < sigma ^ 2 * D.scalarCurvature (T.chain.neck i).center := by
    simpa only [mul_comm] using (div_lt_iff₀ (sq_pos_of_pos hsigma)).mp hRc
  have hnormal := tube.neck_normalized_scalar_center (T.chain.neck i) D
  have hsquare : (T.chain.neck i).scale ^ 2 < sigma ^ 2 := by
    nlinarith [hnormal]
  refine ⟨?_, ?_⟩
  · intro z hz
    have hzread := (A.mem_tail_iff_m28 true hmax0 hmax1).mp (hN hz)
    exact (A.mem_tail_iff_m28 true hc0 hc1).mpr
      ⟨hzread.1, (le_max_left _ _).trans_lt hzread.2⟩
  · nlinarith [(T.chain.neck i).scale_pos]

end PoincareConjecture.M28
