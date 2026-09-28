import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereOpenMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereNullhomotopy
import PoincareConjecture.Proofs.M36.NeckMetricBound











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable local instance standardSphereCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance standardSphereCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance standardSphereTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance standardSphereTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace



theorem StandardCylinderPatch.sphere_mfderiv {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (z : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) z) :
    mfderiv (𝓡 2) (𝓡 3) (StandardCylinderPatch.sphereMap N) z v =
      mfderiv IC (𝓡 3) N.coordinate (z, 0) (v, 0) := by
  have hz : (z, (0 : ℝ)) ∈ univ ×ˢ Ioo (-length) length :=
    ⟨mem_univ z, neg_neg_of_pos N.length_pos, N.length_pos⟩
  have hN := (N.coordinate_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).mdifferentiableAt (by simp)
  have hinc : MDifferentiableAt (𝓡 2) IC (fun q : UnitTwoSphere => (q, (0 : ℝ))) z :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hd : mfderiv (𝓡 2) IC (fun q : UnitTwoSphere => (q, (0 : ℝ))) z =
      (ContinuousLinearMap.id ℝ E2).prod (0 : E2 →L[ℝ] ℝ) := by
    convert! mfderiv_prodMk (mdifferentiableAt_id (I := 𝓡 2) (x := z))
      (mdifferentiableAt_const (I := 𝓡 2) (c := (0 : ℝ))) using 1
    simp [TangentSpace]
  simp only [TangentSpace] at v ⊢
  change mfderiv (𝓡 2) (𝓡 3) (N.coordinate ∘ fun q => (q, (0 : ℝ))) z v = _
  rw [mfderiv_comp z hN hinc, hd]
  rfl



theorem StandardCylinderPatch.sphere_immersion {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (z : UnitTwoSphere) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (StandardCylinderPatch.sphereMap N) z) := by
  have hz : (z, (0 : ℝ)) ∈ univ ×ˢ Ioo (-length) length :=
    ⟨mem_univ z, neg_neg_of_pos N.length_pos, N.length_pos⟩
  have hd := (standardPatchDiffeomorph N).isLocalDiffeomorphAt IC (𝓡 3) ∞ hz
  have hinv : (mfderiv IC (𝓡 3) N.coordinate (z, 0)).IsInvertible :=
    ⟨hd.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  intro u v h
  rw [StandardCylinderPatch.sphere_mfderiv, StandardCylinderPatch.sphere_mfderiv] at h
  exact congrArg Prod.fst (hinv.injective h)



theorem StandardCylinderPatch.sphereCoordinateDifferential_center
    {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (z : UnitTwoSphere) (v : E2) :
    sphereCoordinateDifferential (StandardCylinderPatch.sphereMap N) z z v =
      mfderiv IC (𝓡 3) N.coordinate (z, 0) (v, 0) := by
  simp only [TangentSpace]
  change sphereCoordinateDifferential (fun z => N.coordinate (z, 0)) z z v = _
  rw [sphereCoordinateDifferential_eq (StandardCylinderPatch.contMDiff_sphere N) z
    (mem_chart_source E2 z),
    M36.sphere_chart_inverse_mfderiv]
  exact StandardCylinderPatch.sphere_mfderiv N z v



theorem centeredStandardPatchChart_mfderiv_zero
    {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (z : UnitTwoSphere) (v : E) :
    mfderiv (𝓡 3) (𝓡 3) (centeredStandardPatchChart N z 0) 0 v =
      mfderiv IC (𝓡 3) N.coordinate (z, 0)
        (cylinderHorizontalProjection v, cylinderHeightCovector v) := by
  have hz : (z, (0 : ℝ)) ∈ univ ×ˢ Ioo (-length) length :=
    ⟨mem_univ z, neg_neg_of_pos N.length_pos, N.length_pos⟩
  have hN := (N.coordinate_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).mdifferentiableAt (by simp)
  have hL := (centeredCylinderLift_contMDiff z 0 0).mdifferentiableAt (by simp)
  have hNc : MDifferentiableAt IC (𝓡 3) N.coordinate (centeredCylinderLift z 0 0) := by
    rwa [centeredCylinderLift_zero]
  change mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ centeredCylinderLift z 0) 0 v = _
  rw [mfderiv_comp 0 hNc hL]
  change mfderiv IC (𝓡 3) N.coordinate (centeredCylinderLift z 0 0)
    (mfderiv (𝓡 3) IC (centeredCylinderLift z 0) 0 v) = _
  rw [centeredCylinderLift_mfderiv, centeredCylinderLift_zero, map_zero,
    ← sphere_chart_center_zero z, M36.sphere_chart_inverse_mfderiv]
  rfl



theorem sphereSectionalJetRegion_of_centered_margin
    {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (z : UnitTwoSphere)
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g) {k : ℝ}
    (hmargin : metricTwoJet (g.pullbackCoefficients (centeredStandardPatchChart N z 0)) 0 ∈
      sectionalJetLowerRegion k (e 0) (e 1)) :
    (z, metricTwoJet g.euclideanCoefficients (StandardCylinderPatch.sphereMap N z)) ∈
      sphereSectionalJetRegion (StandardCylinderPatch.sphereMap N) k := by
  let f := centeredStandardPatchChart N z 0
  have hzero : (0 : E) ∈ f.source := by
    rw [mem_centeredStandardPatchChart_source]
    simp only [map_zero, add_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos N.length_pos, N.length_pos⟩
  have h := sectional_lower_of_pullback_twoJet g D f.open_source f.contMDiffOn
    (fun x hx => ⟨(f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩)
    hzero k (e 0) (e 1) hmargin
  have hframe0 : mfderiv (𝓡 3) (𝓡 3) f 0 (e 0) =
      sphereCoordinateDifferential (StandardCylinderPatch.sphereMap N) z z (b 0) := by
    rw [centeredStandardPatchChart_mfderiv_zero,
      StandardCylinderPatch.sphereCoordinateDifferential_center]
    congr 1
    exact cylinderEuclideanEquiv_basis 0
  have hframe1 : mfderiv (𝓡 3) (𝓡 3) f 0 (e 1) =
      sphereCoordinateDifferential (StandardCylinderPatch.sphereMap N) z z (b 1) := by
    rw [centeredStandardPatchChart_mfderiv_zero,
      StandardCylinderPatch.sphereCoordinateDifferential_center]
    congr 1
    exact cylinderEuclideanEquiv_basis 1
  dsimp only at h
  rw [hframe0, hframe1, centeredStandardPatchChart_zero] at h
  refine ⟨z, mem_chart_source E2 z, g.inner_isInvertible _, h.1, ?_⟩
  rw [jetCurvature_metricTwoJet D]
  exact (lt_div_iff₀ h.1).mp h.2




theorem continuousOn_euclidean_twoJet {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (F : RicciFlow 3 E J) :
    ContinuousOn (fun p : ℝ × E => metricTwoJet
      (F.metric p.1).euclideanCoefficients p.2) (J ×ˢ univ) := by
  let B : ℝ × E → MetricCoefficient 3 := fun p => (F.metric p.1).euclideanCoefficients p.2
  have hid (g : RiemannianMetric 3 E) : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext y v w
    simp only [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  have h0 : ContDiffOn ℝ ∞ B (J ×ˢ univ) := by
    simpa only [hid] using contDiffOn_pullbackCoefficients_within F isOpen_univ
      (contMDiff_id.contMDiffOn (s := univ))
  have h1 := contDiffOn_spatialFDeriv_within h0 hJ isOpen_univ
  have h2 := contDiffOn_spatialFDeriv_within h1 hJ isOpen_univ
  exact h0.continuousOn.prodMk (h1.continuousOn.prodMk h2.continuousOn)




theorem exists_standard_sphere_margin {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ length : ℝ, ∃ center : StandardCapSpace,
      ∃ N : StandardCylinderPatch length center,
      ∃ delta : ℝ, 0 < delta ∧
      ∀ t ∈ Icc (0 : ℝ) theta, ∀ z : UnitTwoSphere, ∀ J : MetricTwoJet 3,
        ‖J - metricTwoJet (S.flow.metric t).euclideanCoefficients
          (StandardCylinderPatch.sphereMap N z)‖ ≤ delta →
          (z, J) ∈ sphereSectionalJetRegion (StandardCylinderPatch.sphereMap N) (1 / 4) := by
  obtain ⟨epsilon, _hepsilon, center, N, hmargin⟩ :=
    exists_standard_whole_collar S (C := 1) zero_lt_one htheta0 htheta
  have hsub : Icc (0 : ℝ) theta ⊆ Ico (0 : ℝ) S.flow.base.lifetime := by
    rw [S.lifetime_one]
    exact fun _ ht => ⟨ht.1, ht.2.trans_lt htheta⟩
  have hc : ContinuousOn (fun p : ℝ × UnitTwoSphere =>
      metricTwoJet (S.flow.metric p.1).euclideanCoefficients
        (StandardCylinderPatch.sphereMap N p.2)) (Icc (0 : ℝ) theta ×ˢ univ) :=
    (continuousOn_euclidean_twoJet
    (uniqueDiffOn_Ico 0 S.flow.base.lifetime) S.flow.base.flow).comp
      (continuous_fst.prodMk
        ((StandardCylinderPatch.sphereMap N).continuous.comp continuous_snd)).continuousOn
      (fun _ hp => ⟨hsub hp.1, mem_univ _⟩)
  obtain ⟨delta, hdelta, hkeep⟩ := exists_uniform_sphere_jet_margin
    (StandardCylinderPatch.contMDiff_sphere N) (1 / 4) isCompact_Icc
    (fun t z => metricTwoJet (S.flow.metric t).euclideanCoefficients
      (StandardCylinderPatch.sphereMap N z)) hc
    (fun t ht z => sphereSectionalJetRegion_of_centered_margin N z
      (S.flow.metric t) (S.flow.connection t) (hmargin t ht z).2)
  exact ⟨epsilon⁻¹, center, N, delta, hdelta, hkeep⟩

end PoincareConjecture.M44
