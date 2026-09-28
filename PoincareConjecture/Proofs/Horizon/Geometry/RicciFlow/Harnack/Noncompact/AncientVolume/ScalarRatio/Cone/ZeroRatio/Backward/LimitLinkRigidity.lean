import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.AngularLower
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hypersurface.UmbilicSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000

open Set PoincareConjecture Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.AncientVolume.ScalarRatio

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_metric_preserving_sphere_diffeomorph_of_unit_umbilic
    {n : ℕ} (hn : 1 ≤ n) {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S] [IsManifold (𝓡 n) ∞ S]
    [CompactSpace S] [ConnectedSpace S]
    (g : RiemannianMetric n S)
    (f N : S → EuclideanSpace ℝ (Fin (n + 1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f)
    (hN : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ N)
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) f z))
    (hunit : ∀ z, ‖N z‖ = 1)
    (hderiv : ∀ z, mfderiv (𝓡 n) (𝓡 (n + 1)) N z =
      mfderiv (𝓡 n) (𝓡 (n + 1)) f z)
    (hinj : Function.Injective f)
    (hmetric : ∀ z (v w : TangentSpace (𝓡 n) z),
      g.inner z v w = inner ℝ (mfderiv (𝓡 n) (𝓡 (n + 1)) f z v)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) f z w)) :
    ∃ e : Diffeomorph (𝓡 n) (𝓡 n) S (UnitSphere n) ∞,
      (∀ z, (e z : EuclideanSpace ℝ (Fin (n + 1))) = N z) ∧
      ∀ z (v w : TangentSpace (𝓡 n) z),
        g.inner z v w = (roundSphereMetric n).inner (e z)
          (mfderiv (𝓡 n) (𝓡 n) e z v) (mfderiv (𝓡 n) (𝓡 n) e z w) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨c, hc, _⟩ :=
    Poincare.Geometry.Riemannian.Hypersurface.exists_center_range_sphere_of_unit_derivative
      hn f N hf hN himm hunit hderiv
  have hmem : ∀ z, N z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hunit
  let F : S → UnitSphere n := Set.codRestrict N _ hmem
  have hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F := hN.codRestrict_sphere hmem
  have hFi : Function.Injective F := by
    intro x y hxy
    apply hinj
    have hxyN : N x = N y := congrArg Subtype.val hxy
    have hx : f x = c + N x := sub_eq_iff_eq_add.mp (hc x)
    have hy : f y = c + N y := sub_eq_iff_eq_add.mp (hc y)
    exact hx.trans ((congrArg (fun v => c + v) hxyN).trans hy.symm)
  have hFs : Function.Surjective F :=
    Poincare.Geometry.Riemannian.Hypersurface.surjective_unitMap_of_injective_mfderiv
      hn N hN hunit (fun z => by rw [hderiv z]; exact himm z)
  have hFderiv : ∀ z, Function.Injective
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (fun y => (F y : EuclideanSpace ℝ (Fin (n + 1)))) z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) N z)
    rw [hderiv z]
    exact himm z
  let e := (Poincare.Geometry.Riemannian.Convexity.isLocalDiffeomorph_sphere_of_injective_ambient_mfderiv
    hF hFderiv).diffeomorphOfBijective ⟨hFi, hFs⟩
  refine ⟨e, fun _ => rfl, ?_⟩
  intro z v w
  have hd := mfderiv_comp z
    ((contMDiff_coe_sphere (n := n) (m := ∞) (e z)).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiable (by simp) z)
  have hdf : (mfderiv (𝓡 n) (𝓡 (n + 1))
      ((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) (e z)).comp
      (mfderiv (𝓡 n) (𝓡 n) e z) = mfderiv (𝓡 n) (𝓡 (n + 1)) f z := by
    rw [← hd]
    change mfderiv (𝓡 n) (𝓡 (n + 1)) N z = _
    exact hderiv z
  rw [roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner]
  change g.inner z v w = inner ℝ
    (((mfderiv (𝓡 n) (𝓡 (n + 1))
      ((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) (e z)).comp
      (mfderiv (𝓡 n) (𝓡 n) e z)) v)
    (((mfderiv (𝓡 n) (𝓡 (n + 1))
      ((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) (e z)).comp
      (mfderiv (𝓡 n) (𝓡 n) e z)) w)
  rw [hdf]
  exact hmetric z v w

theorem nonempty_chordal_sphere_isometry_of_unit_umbilic
    {n : ℕ} (hn : 1 ≤ n) {S : Type*} [MetricSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S] [IsManifold (𝓡 n) ∞ S]
    [CompactSpace S] [ConnectedSpace S]
    (g : RiemannianMetric n S)
    (hdiam : ∀ x y : S, dist x y ≤ 2)
    (hangle : ∀ x y : S,
      g.edist x y = ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)))
    (f N : S → EuclideanSpace ℝ (Fin (n + 1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f)
    (hN : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ N)
    (himm : ∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) f z))
    (hunit : ∀ z, ‖N z‖ = 1)
    (hderiv : ∀ z, mfderiv (𝓡 n) (𝓡 (n + 1)) N z =
      mfderiv (𝓡 n) (𝓡 (n + 1)) f z)
    (hinj : Function.Injective f)
    (hmetric : ∀ z (v w : TangentSpace (𝓡 n) z),
      g.inner z v w = inner ℝ (mfderiv (𝓡 n) (𝓡 (n + 1)) f z v)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) f z w)) :
    Nonempty (S ≃ᵢ UnitSphere n) := by
  obtain ⟨e, _, hinner⟩ := exists_metric_preserving_sphere_diffeomorph_of_unit_umbilic
    hn g f N hf hN himm hunit hderiv hinj hmetric
  have he : Isometry e := by
    apply Isometry.of_dist_eq
    intro x y
    have h := g.edist_diffeomorph (roundSphereMetric n) e hinner x y
    rw [hangle, roundSphereMetric_edist_eq_angle hn] at h
    have ha := congrArg ENNReal.toReal h
    simp only [ENNReal.toReal_ofReal (Real.arccos_nonneg _)] at ha
    have htwo : dist (e x) (e y) ≤ 2 := by
      have hx : ‖(e x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using (e x).property
      have hy : ‖(e y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using (e y).property
      simpa only [Subtype.dist_eq, hx, hy, show (1 : ℝ) + 1 = 2 by norm_num] using
        dist_le_norm_add_norm (e x : EuclideanSpace ℝ (Fin (n + 1)))
          (e y : EuclideanSpace ℝ (Fin (n + 1)))
    have hcos := congrArg Real.cos ha
    rw [Real.cos_arccos (by nlinarith [hdiam x y, dist_nonneg (x := x) (y := y)])
      (by nlinarith [sq_nonneg (dist x y)]),
      Real.cos_arccos (by nlinarith [dist_nonneg (x := e x) (y := e y)])
        (by nlinarith [sq_nonneg (dist (e x) (e y))])] at hcos
    nlinarith [dist_nonneg (x := x) (y := y), dist_nonneg (x := e x) (y := e y)]
  exact ⟨{ toEquiv := e.toEquiv, isometry_toFun := he }⟩

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

theorem nonempty_asymptoticLink_chordal_isometry_of_unit_umbilic
    {m n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
    (g : RiemannianMetric m M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) (hn : 1 ≤ n) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ (hcover : ∀ x : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (z : d.Level), (d.levelHomeomorph z).1 = x),
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    ∀ (f N : AsymptoticConeUnitSlice p hc → EuclideanSpace ℝ (Fin (n + 1))),
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f → ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ N →
      (∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) f z)) →
      (∀ z, ‖N z‖ = 1) →
      (∀ z, mfderiv (𝓡 n) (𝓡 (n + 1)) N z = mfderiv (𝓡 n) (𝓡 (n + 1)) f z) →
      (∀ x y, dist x y ≤ dist (f x) (f y)) →
      (∀ z (v w : TangentSpace (𝓡 n) z), (unitSliceMetric hcover).inner z v w =
        inner ℝ (mfderiv (𝓡 n) (𝓡 (n + 1)) f z v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) f z w)) →
      Nonempty (AsymptoticLink p hc ≃ᵢ UnitSphere n) := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hcomplete
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  dsimp only
  intro hcover
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  intro f N hf hN himm hunit hderiv hsep hmetric
  letI : PathConnectedSpace (AsymptoticConeUnitSlice p hc) :=
    g.pathConnectedSpace_asymptoticConeUnitSlice_of_chartedSpace D hcomplete hsec p hn
      (unitSliceChartedSpace hc n hcover)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa only [hxy, dist_self] using hsep x y) dist_nonneg
  obtain ⟨e⟩ := nonempty_chordal_sphere_isometry_of_unit_umbilic hn
    (unitSliceMetric hcover) (fun x y => unitSlice_dist_le_two x y)
    (g.unitSlice_metric_edist_eq_angle_of_metricComplete D hcomplete hsec p hn hcover)
    f N hf hN himm hunit hderiv hinj hmetric
  exact ⟨(asymptoticConeUnitIsometry hc).trans e⟩

end PoincareConjecture.RiemannianMetric
