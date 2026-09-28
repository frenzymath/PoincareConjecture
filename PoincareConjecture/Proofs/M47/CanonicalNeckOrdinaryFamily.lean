import PoincareConjecture.Proofs.M47.CanonicalNeckBufferedFamily
import PoincareConjecture.Proofs.M47.CanonicalNeckCompressedCertificate
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem compressed_neck_metric_pullback
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (h : RiemannianMetric 3 M)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    neckAxialTensorPullback lambda c (roundCylinderPullback h N.coordinate_map) z v w =
      roundCylinderPullback h (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w := by
  have hz' : neckAxialSpaceMap lambda c z ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨mem_univ _, neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hc
      ⟨hz.1.le, hz.2.le⟩⟩
  have hNd := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz')).mdifferentiableAt (by simp)
  have hAd := ((neckAxialSpaceMap_contMDiff lambda c) z).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z hNd hAd
  simp only [neckAxialTensorPullback, roundCylinderPullback, Function.comp_apply,
    hchain, ContinuousLinearMap.comp_apply, neckAxialSpaceMap_mfderiv]

theorem exists_eventually_buffered_ordinary_necks [T3Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (G : RicciFlow 3 M (Icc a b)) (t0 : Icc a b)
    (N : EpsilonNeck (G.metric t0.val))
    (hconnection : N.connection = G.connection t0.val)
    (hbottom : a < t0.val - ((G.connection t0.val).scalarCurvature N.center)⁻¹)
    (htop : t0.val < b)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => (G.connection t0.val).scalarCurvature N.center *
        roundCylinderPullback
          (G.metric (t0.val + u / (G.connection t0.val).scalarCurvature N.center))
          N.coordinate_map z v w)) :
    ∃ lambda : ℝ, lambda ∈ Ioo (0 : ℝ) 1 ∧
      ∀ᶠ p : Icc a b × M in 𝓝 (t0, N.center),
        0 < (G.connection p.1.val).scalarCurvature p.2 ∧
        (∀ u ∈ Icc (-1 : ℝ) 0,
          p.1.val + u / (G.connection p.1.val).scalarCurvature p.2 ∈ Icc a b) ∧
        ∃ N' : EpsilonNeck (G.metric p.1.val),
          N'.epsilon = N.epsilon ∧ N'.center = p.2 ∧
          N'.connection = G.connection p.1.val ∧
          N'.carrier = compressedNeckCarrier N lambda (N.coordinate_inverse p.2).2 ∧
          N'.carrier ⊆ N.carrier ∧
          N'.coordinate_map = N.coordinate_map ∘
            neckAxialSpaceMap lambda (N.coordinate_inverse p.2).2 ∧
          RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
            (fun u z v w => (G.connection p.1.val).scalarCurvature p.2 *
              roundCylinderPullback
                (G.metric (p.1.val + u / (G.connection p.1.val).scalarCurvature p.2))
                N'.coordinate_map z v w) := by
  let T : Icc a b × M → ℝ := fun p => p.1.val
  let Q : Icc a b × M → ℝ := fun p => (G.connection p.1.val).scalarCurvature p.2
  let c : Icc a b × M → ℝ := fun p => (N.coordinate_inverse p.2).2
  have hT : ContinuousAt T (t0, N.center) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt
  have hmap : Continuous (fun p : Icc a b × M => (p.1.val, p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hQ : ContinuousAt Q (t0, N.center) :=
    ((hC.scalar_regular 3 M (Icc a b) G).continuousOn.comp_continuous hmap
      (fun p => ⟨p.1.property, mem_univ p.2⟩)).continuousAt
  have hcenter : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hc : ContinuousAt c (t0, N.center) := by
    have haxis : ContinuousAt (fun y : M => (N.coordinate_inverse y).2) N.center :=
      (N.coordinate_inverse_smooth.continuousOn.continuousAt
        (N.carrier_open.mem_nhds hcenter)).snd
    exact haxis.comp (f := (Prod.snd : Icc a b × M → M))
      (x := (t0, N.center)) continuous_snd.continuousAt
  have hc0 : c (t0, N.center) = 0 := by
    have hmem := N.center_on_central_sphere
    rw [N.central_sphere_eq] at hmem
    obtain ⟨⟨q, s⟩, ⟨_hq, hs⟩, hpoint⟩ := hmem
    have hs0 : s = 0 := hs
    subst s
    have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
    have hinv := N.coordinate_inverse_coordinate_map_of_axial_mem (z := (q, 0)) hzero
    dsimp only [c]
    rw [← hpoint]
    exact congrArg Prod.snd hinv
  have hQ0 : 0 < Q (t0, N.center) := by
    change 0 < (G.connection t0.val).scalarCurvature N.center
    rw [← hconnection]
    exact N.scalar_center_pos
  obtain ⟨lambda, hlambda, hnear⟩ := exists_eventually_buffered_normalized_neck_family
    hab G N hT hQ hc hc0 hQ0 hbottom htop hfamily
  refine ⟨lambda, hlambda, ?_⟩
  have hcarrier : ∀ᶠ p : Icc a b × M in 𝓝 (t0, N.center), p.2 ∈ N.carrier :=
    (N.carrier_open.preimage continuous_snd).mem_nhds hcenter
  filter_upwards [hnear, hcarrier] with p hp hx
  have hnormalized : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => Q p * roundCylinderPullback (G.metric (T p + u / Q p))
        (N.coordinate_map ∘ neckAxialSpaceMap lambda (c p)) z v w) := by
    apply hp.2.2.2.congr_cylinder
    intro u _hu z hz v w
    exact congrArg (fun q : ℝ => Q p * q)
      (compressed_neck_metric_pullback N _ hlambda hp.2.1 hz v w)
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hclose : RoundCylinderClose N.epsilon 0
      (fun z v w => Q p * roundCylinderPullback (G.metric (T p))
        (N.coordinate_map ∘ neckAxialSpaceMap lambda (c p)) z v w) := by
    have h : RoundCylinderClose N.epsilon 0
        (fun z v w => Q p * roundCylinderPullback (G.metric (T p + 0 / Q p))
          (N.coordinate_map ∘ neckAxialSpaceMap lambda (c p)) z v w) :=
      ⟨hnormalized.1 0 hzero, hnormalized.2.choose, hnormalized.2.choose_spec.1,
        hnormalized.2.choose_spec.2 0 hzero⟩
    simpa only [zero_div, add_zero] using h
  obtain ⟨N', hepsilon, hcenter', hcarrier', hcoordinate, _hinverse,
    _hsphere, hconnection', _hcoordinateHEq⟩ :=
    exists_compressed_neck_of_normalized_comparison N hlambda hp.2.1 p.2 hx rfl
      (G.connection p.1.val) hp.1 hclose
  refine ⟨hp.1, hp.2.2.1, N', hepsilon, hcenter', hconnection', hcarrier', ?_,
    hcoordinate, ?_⟩
  · rw [hcarrier']
    exact inter_subset_left
  · rw [hcoordinate]
    exact hnormalized

end PoincareConjecture.Proofs.M47
