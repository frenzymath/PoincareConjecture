import PoincareConjecture.Proofs.M35.CapGeometry.NeckBufferedBall
import PoincareConjecture.Proofs.M35.CapGeometry.NeckScalarFloor
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.StandardCylinderPatch

theorem scaled_central_sphere_ball_subset_carrier_of_axial_cutoff
    {epsilon ell : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (A : StandardCylinderAtlas)
    (g : RiemannianMetric 3 StandardCapSpace) (Q : ℝ) (hQ : 0 < Q)
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 24)
    (hell : 0 < ell) (hlong : ell < epsilon⁻¹)
    (hclose : StandardSpatialCylinderClose A g epsilon Q N) (q : UnitTwoSphere) :
    g.ball (N.coordinate (q, 0)) (ell / (2 * Real.sqrt Q)) ⊆ N.carrier := by
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g Q hQ
  have hscaled : RoundCylinderClose epsilon 0 (roundCylinderPullback G N.coordinate) := hclose
  have hball := M13.homothety_ball_image g G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) (N.coordinate (q, 0))
    (ell / (2 * Real.sqrt Q))
  have hroot : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hradius : Real.sqrt Q * (ell / (2 * Real.sqrt Q)) = ell / 2 := by
    field_simp
  change id '' g.ball (N.coordinate (q, 0)) (ell / (2 * Real.sqrt Q)) =
    G.ball (N.coordinate (q, 0)) (Real.sqrt Q * (ell / (2 * Real.sqrt Q))) at hball
  rw [image_id, hradius] at hball
  rw [hball]
  exact N.central_sphere_ball_subset_carrier_of_axial_cutoff G he hesmall
    (by norm_num) hell hlong hscaled q

theorem exists_curvature_radius_near_central_sphere
    {epsilon : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (A : StandardCylinderAtlas)
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hR : Continuous D.scalarCurvature)
    (Q : ℝ) (hQ : 0 < Q) (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 24)
    (hlong : 8 < epsilon⁻¹) (hclose : StandardSpatialCylinderClose A g epsilon Q N)
    (q : UnitTwoSphere) (hscalar : Q / 2 < D.scalarCurvature (N.coordinate (q, 0)))
    (y : StandardCapSpace)
    (hy : y ∈ g.ball (N.coordinate (q, 0)) (1 / (2 * Real.sqrt Q))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 / Real.sqrt Q ∧
      scalarCurvatureSupOn g D (g.ball y r) = r⁻¹ ^ 2 ∧
      closure (g.ball y r) ⊆ N.carrier ∧ IsCompact (closure (g.ball y r)) := by
  have hcomm (a b : StandardCapSpace) : g.edist a b = g.edist b a :=
    @edist_comm StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace a b
  have htriangle (a b c : StandardCapSpace) :
      g.edist a c ≤ g.edist a b + g.edist b c :=
    @edist_triangle StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace a b c
  have hcontinuous : Continuous (fun z : StandardCapSpace => g.edist y z) :=
    (@continuous_edist StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace).comp
      (continuous_const.prodMk continuous_id)
  let p := N.coordinate (q, 0)
  let b := 2 / Real.sqrt Q
  let d := 1 / (2 * Real.sqrt Q)
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hb : 0 < b := div_pos (by norm_num) hsqrt
  have hd : 0 < d := div_pos (by norm_num) (mul_pos (by norm_num) hsqrt)
  have hdb : d < b := by
    dsimp only [b, d]
    rw [div_mul_eq_div_div]
    exact (div_lt_div_iff_of_pos_right hsqrt).mpr (by norm_num)
  have hy' : g.edist p y < ENNReal.ofReal d := hy
  have hpball : p ∈ g.ball y b := by
    change g.edist y p < ENNReal.ofReal b
    rw [hcomm y p]
    exact hy'.trans_le (ENNReal.ofReal_le_ofReal hdb.le)
  have hcompact := Proofs.M09.isCompact_closure_metric_ball g hcomplete y b
  have hbounded : BddAbove (range fun z : g.ball y b => D.scalarCurvature z.1) := by
    rw [← image_eq_range]
    exact (hcompact.bddAbove_image hR.continuousOn).mono (image_mono subset_closure)
  have hsup : D.scalarCurvature p ≤ scalarCurvatureSupOn g D (g.ball y b) :=
    le_csSup hbounded ⟨⟨p, hpball⟩, rfl⟩
  have hbscale : b ^ 2 = 4 / Q := by
    dsimp only [b]
    rw [div_pow, Real.sq_sqrt hQ.le]
    norm_num
  have hcross : 1 ≤ b ^ 2 * scalarCurvatureSupOn g D (g.ball y b) := by
    have hscalar' : Q / 2 < scalarCurvatureSupOn g D (g.ball y b) := hscalar.trans_le hsup
    have h := mul_lt_mul_of_pos_left hscalar' (div_pos (by norm_num : (0 : ℝ) < 4) hQ)
    have htwo : (4 / Q) * (Q / 2) = 2 := by field_simp; ring
    rw [htwo, ← hbscale] at h
    linarith
  have hclosed : closure (g.ball y b) ⊆ {z : StandardCapSpace | g.edist y z ≤ ENNReal.ofReal b} :=
    closure_minimal (fun z hz => (show g.edist y z < ENNReal.ofReal b from hz).le)
      (isClosed_le hcontinuous continuous_const)
  have houter := N.scaled_central_sphere_ball_subset_carrier_of_axial_cutoff A g Q hQ
    he hesmall (by norm_num : (0 : ℝ) < 8) hlong hclose q
  have hsize : d + b ≤ 8 / (2 * Real.sqrt Q) := by
    dsimp only [d, b]
    rw [div_mul_eq_div_div, div_mul_eq_div_div]
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hsqrt).mpr (by norm_num)
  have hinside : closure (g.ball y b) ⊆ N.carrier := by
    intro z hz
    apply houter
    change g.edist p z < ENNReal.ofReal (8 / (2 * Real.sqrt Q))
    calc
      g.edist p z ≤ g.edist p y + g.edist y z := htriangle p y z
      _ ≤ g.edist p y + ENNReal.ofReal b :=
        add_le_add le_rfl (show g.edist y z ≤ ENNReal.ofReal b from hclosed hz)
      _ < ENNReal.ofReal d + ENNReal.ofReal b :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hy'
      _ = ENNReal.ofReal (d + b) := (ENNReal.ofReal_add hd.le hb.le).symm
      _ ≤ ENNReal.ofReal (8 / (2 * Real.sqrt Q)) := ENNReal.ofReal_le_ofReal hsize
  obtain ⟨r, hr, hrb, hscale, hcompactr⟩ :=
    M35.exists_scalar_curvature_radius_le g D hcomplete hR y hb hcross
  exact ⟨r, hr, hrb, hscale,
    (closure_mono (fun z hz => hz.trans_le (ENNReal.ofReal_le_ofReal hrb))).trans hinside,
    hcompactr⟩

end PoincareConjecture.StandardCylinderPatch
