import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Shift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Nonsingular
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.SegmentRegular
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.FiniteDistanceSupports
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Finite






noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_distance_laplacian_upper_support_of_finite
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M]
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      -(m : ℝ) * k ^ 2 * g.inner y v v ≤ D.ricci y v v)
    (p x : M) (hpx : p ≠ x) (hfinite : g.edist p x ≠ ⊤) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      D.laplacian rho x ≤
        2 * (m : ℝ) / (g.edist p x).toReal + (m : ℝ) * k := by
  have hdpos : 0 < g.edist p x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m + 1)))
        (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
    exact edist_pos.mpr hpx
  have hr : 0 < (g.edist p x).toReal :=
    ENNReal.toReal_pos hdpos.ne' hfinite
  let R := (g.edist p x).toReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete_of_finite hcomplete hfinite
  obtain ⟨L, e, hL, he, he0, hed, hrad⟩ :=
    g.exists_orthonormal_radial_exponential_of_metricComplete hcomplete (γ (1 / 4)) hR
  have hgeo := fun w hw => (hrad w hw).1
  have hspeed := fun w hw t ht => ((hrad w hw).2 t ht).1
  obtain ⟨v, hv, hnorm, hx, hsplit, hmatch⟩ := g.exists_quarter_shifted_radial_vector
    hε hγ hγ0 hγ1 hmin (by dsimp [R]; linarith) L e hL he0 hed hgeo
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; positivity)
  have heorigin := he.contMDiffAt (Metric.isOpen_ball.mem_nhds
    (show (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.ball 0 R by simpa using hR))
  have hinit := isInvertible_mfderiv_zero_of_chart_derivative
    (heorigin.mdifferentiableAt (by simp)) he0 hed
  have hback : e ((-1 / 3 : ℝ) • v) = p := by
    have h := (hmatch (-1 / 3) (by norm_num)).self_of_nhds
    norm_num only [show (3 / 4 : ℝ) * (-1 / 3) + 1 / 4 = 0 by ring] at h
    simpa only [neg_div] using h.trans hγ0
  have hminback : g.edist (e ((-1 / 3 : ℝ) • v)) (e v) =
      ENNReal.ofReal ((4 / 3 : ℝ) * ‖v‖) := by
    rw [hback, hx, hnorm, show (4 / 3 : ℝ) * ((3 / 4) * (g.edist p x).toReal) =
      (g.edist p x).toReal by ring, ENNReal.ofReal_toReal hfinite]
  have hend := g.isInvertible_mfderiv_of_minimizing_backward_extension
    D he hinit hgeo hspeed hv hv0 hminback
  have htailmin : g.edist (γ (1 / 4)) (e v) = ENNReal.ofReal ‖v‖ := by
    have h := hmin (1 / 4) (by norm_num) 1 (by norm_num)
    rw [hγ1] at h
    rw [hx, h, hnorm, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4),
      ENNReal.ofReal_toReal hfinite]
    norm_num
  have hi := g.isInvertible_mfderiv_on_minimizing_segment D he he0 hinit
    hgeo hspeed hv hv0 htailmin hend
  have hbound : ∀ w ∈ Metric.ball 0 R,
      g.edist (γ (1 / 4)) (e w) ≤ ENNReal.ofReal ‖w‖ := by
    intro w hw
    simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hrad w hw).2 1 (by simp)).2
  have hquarter_finite : g.edist p (γ (1 / 4)) ≠ ⊤ := by
    rw [← hγ0, hmin 0 (by norm_num) (1 / 4) (by norm_num)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  exact g.upper_support_of_regular_minimizing_tail_of_finite D hm
    p (γ (1 / 4)) x he
    (g.pullbackCoefficients_zero_of_orthonormal (γ (1 / 4)) heorigin he0 hed hL)
    hgeo hbound hk hRic hv hv0 hx hsplit hquarter_finite
    (by rw [hnorm]; linarith) hi

end PoincareConjecture.RiemannianMetric
