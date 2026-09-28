import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereJetMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_AxialJetMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_CylinderPlaneRank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

noncomputable local instance sphereOpenCoefficientNorm : NormedAddCommGroup (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sphereOpenCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance sphereOpenTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance sphereOpenTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

noncomputable def sphereCoordinateDifferential (sigma : UnitTwoSphere → E)
    (z x : UnitTwoSphere) : E2 →L[ℝ] E :=
  fderiv ℝ (sigma ∘ (chartAt E2 z).symm) ((chartAt E2 z) x)

theorem continuousAt_sphereCoordinateDifferential {sigma : UnitTwoSphere → E}
    (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma) (z : UnitTwoSphere)
    {x : UnitTwoSphere} (hx : x ∈ (chartAt E2 z).source) :
    ContinuousAt (sphereCoordinateDifferential sigma z) x := by
  have hs : ContDiff ℝ ∞ (sigma ∘ (chartAt E2 z).symm) :=
    contMDiff_iff_contDiff.mp (hsigma.comp (M36.sphere_chart_inverse_contMDiff z))
  exact ((hs.contDiffAt.fderiv_right (m := ∞) (by simp)).continuousAt).comp
    ((chartAt E2 z).continuousOn.continuousAt ((chartAt E2 z).open_source.mem_nhds hx))

def sphereSectionalJetRegion (sigma : UnitTwoSphere → E) (k : ℝ) :
    Set (UnitTwoSphere × MetricTwoJet 3) :=
  {p | ∃ z : UnitTwoSphere, p.1 ∈ (chartAt E2 z).source ∧
    p.2 ∈ sectionalJetLowerRegion k
      (sphereCoordinateDifferential sigma z p.1 (b 0))
      (sphereCoordinateDifferential sigma z p.1 (b 1))}

theorem isOpen_sphereSectionalJetRegion {sigma : UnitTwoSphere → E}
    (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma) (k : ℝ) :
    IsOpen (sphereSectionalJetRegion sigma k) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x, J⟩ ⟨z, hx, hJ⟩
  have hD := (continuousAt_sphereCoordinateDifferential hsigma z hx).comp
    (continuousAt_fst (p := (x, J)))
  have hu := hD.clm_apply (continuousAt_const (y := b 0))
  have hv := hD.clm_apply (continuousAt_const (y := b 1))
  let G (p : UnitTwoSphere × MetricTwoJet 3) := collarJetGram
    (sphereCoordinateDifferential sigma z p.1 (b 0))
    (sphereCoordinateDifferential sigma z p.1 (b 1)) p.2
  have hG : ContinuousAt G (x, J) := by
    dsimp [G, collarJetGram]
    fun_prop
  have hR := continuousAt_jetCurvature_family continuousAt_snd hJ.1 hu hv hu hv
  have hmargin : 0 < jetCurvature J
      (sphereCoordinateDifferential sigma z x (b 0))
      (sphereCoordinateDifferential sigma z x (b 1))
      (sphereCoordinateDifferential sigma z x (b 0))
      (sphereCoordinateDifferential sigma z x (b 1)) - k * G (x, J) :=
    sub_pos.mpr hJ.2.2
  filter_upwards [continuousAt_fst.eventually ((chartAt E2 z).open_source.mem_nhds hx),
    continuousAt_snd.eventually ((isOpen_ricciFlowOperator_domain 3).mem_nhds hJ.1),
    hG.eventually (lt_mem_nhds hJ.2.1),
    (hR.sub (continuousAt_const.mul hG)).eventually (lt_mem_nhds hmargin)]
      with p hp hI hGram hLower
  exact ⟨z, hp, hI, hGram, sub_pos.mp hLower⟩

theorem exists_uniform_sphere_jet_margin {sigma : UnitTwoSphere → E}
    (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma) (k : ℝ)
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (J : X → UnitTwoSphere → MetricTwoJet 3)
    (hJ : ContinuousOn (fun p : X × UnitTwoSphere => J p.1 p.2) (K ×ˢ univ))
    (hmargin : ∀ t ∈ K, ∀ z, (z, J t z) ∈ sphereSectionalJetRegion sigma k) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ K, ∀ z, ∀ J' : MetricTwoJet 3,
      ‖J' - J t z‖ ≤ delta → (z, J') ∈ sphereSectionalJetRegion sigma k := by
  let L := (fun p : X × UnitTwoSphere => (p.2, J p.1 p.2)) '' (K ×ˢ univ)
  have hL : IsCompact L := (hK.prod isCompact_univ).image_of_continuousOn
    (continuousOn_snd.prodMk hJ)
  have hsub : L ⊆ sphereSectionalJetRegion sigma k := by
    rintro _ ⟨⟨t, z⟩, ht, rfl⟩
    exact hmargin t ht.1 z
  obtain ⟨delta, hdelta, hinside⟩ :=
    hL.exists_cthickening_subset_open (isOpen_sphereSectionalJetRegion hsigma k) hsub
  refine ⟨delta, hdelta, ?_⟩
  intro t ht z J' hnear
  apply hinside
  apply Metric.mem_cthickening_of_dist_le (z, J') (z, J t z) delta L
    (show (z, J t z) ∈ L from ⟨(t, z), ⟨ht, mem_univ z⟩, rfl⟩)
  simpa only [Prod.dist_eq, dist_self, dist_eq_norm, max_eq_right (norm_nonneg _)] using hnear

theorem sphereCoordinateDifferential_eq {sigma : UnitTwoSphere → E}
    (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma) (z : UnitTwoSphere)
    {x : UnitTwoSphere} (hx : x ∈ (chartAt E2 z).source) :
    sphereCoordinateDifferential sigma z x =
      (mfderiv (𝓡 2) (𝓡 3) sigma x).comp
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 z).symm ((chartAt E2 z) x)) := by
  rw [sphereCoordinateDifferential, ← mfderiv_eq_fderiv,
    mfderiv_comp _ ((hsigma _).mdifferentiableAt (by simp))
      (((M36.sphere_chart_inverse_contMDiff z) _).mdifferentiableAt (by simp))]
  rw [(chartAt E2 z).left_inv hx]

theorem sphere_tangent_mem_coordinate_span {sigma : UnitTwoSphere → E}
    (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma) (z : UnitTwoSphere)
    {x : UnitTwoSphere} (hx : x ∈ (chartAt E2 z).source)
    (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓡 2) (𝓡 3) sigma x v ∈ Submodule.span ℝ
      ({sphereCoordinateDifferential sigma z x (b 0),
        sphereCoordinateDifferential sigma z x (b 1)} : Set E) := by
  have hi : (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 z).symm ((chartAt E2 z) x)).IsInvertible := by
    convert! isInvertible_mfderivWithin_extChartAt_symm
      (I := 𝓡 2) ((extChartAt (𝓡 2) z).map_source (by simpa using hx)) using 1
    simp
  obtain ⟨w, hw⟩ := hi.surjective v
  apply cylinder_plane_mem_span
  refine ⟨w, ?_⟩
  rw [sphereCoordinateDifferential_eq hsigma z hx]
  change mfderiv (𝓡 2) (𝓡 3) sigma x
    (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 z).symm ((chartAt E2 z) x) w) = _
  rw [hw]

theorem sectional_lower_of_sphereJetRegion
    {sigma : UnitTwoSphere → E} (hsigma : ContMDiff (𝓡 2) (𝓡 3) ∞ sigma)
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) {x : UnitTwoSphere} {k : ℝ}
    (hJ : (x, metricTwoJet g.euclideanCoefficients (sigma x)) ∈
      sphereSectionalJetRegion sigma k)
    (u v : TangentSpace (𝓡 2) x)
    (hgram : 0 < g.inner (sigma x) (mfderiv (𝓡 2) (𝓡 3) sigma x u)
      (mfderiv (𝓡 2) (𝓡 3) sigma x u) *
      g.inner (sigma x) (mfderiv (𝓡 2) (𝓡 3) sigma x v)
        (mfderiv (𝓡 2) (𝓡 3) sigma x v) -
      (g.inner (sigma x) (mfderiv (𝓡 2) (𝓡 3) sigma x u)
        (mfderiv (𝓡 2) (𝓡 3) sigma x v)) ^ 2) :
    k < D.sectionalCurvature (sigma x) (mfderiv (𝓡 2) (𝓡 3) sigma x u)
      (mfderiv (𝓡 2) (𝓡 3) sigma x v) := by
  obtain ⟨z, hx, hz⟩ := hJ
  have hlower : k < D.sectionalCurvature (sigma x)
      (sphereCoordinateDifferential sigma z x (b 0))
      (sphereCoordinateDifferential sigma z x (b 1)) := by
    apply (lt_div_iff₀ hz.2.1).mpr
    rw [← jetCurvature_metricTwoJet D]
    exact hz.2.2
  exact sectional_lower_on_physical_plane D (sigma x) hz.2.1 hlower
    (sphere_tangent_mem_coordinate_span hsigma z hx u)
    (sphere_tangent_mem_coordinate_span hsigma z hx v) hgram

end PoincareConjecture.M44
