import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Surface.Evolution
import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional
import PoincareConjecture.Proofs.Horizon.Topology.Covering.SimplyConnected











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TwoDimensionalAncientRoundCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M}



theorem exists_evolving_sphere_cover_at_terminal_scale
    (R : TwoDimensionalAncientRoundCertificate K) (p : M) :
    ∃ q : UnitTwoSphere → M,
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧ IsCoveringMap q ∧
      ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (K.flow.metric t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
          (mfderiv (𝓡 2) (𝓡 2) q x w) =
            (2 / (K.flow.connection 0).scalarCurvature p - 2 * t) *
              (roundSphereMetric 2).inner x v w := by
  let : CompactSpace M := R.compact
  obtain ⟨hr, q, hq, hsurj, hlocal, hmetric, _⟩ :=
    exists_scalarNormalized_roundSurface_cover (K.flow.metric 0) (K.flow.connection 0)
      (R.round_at_all_times 0 le_rfl) p
  refine ⟨q, hq, hsurj, hlocal,
    isLocalHomeomorph_iff_isCoveringMap.mp hlocal.isLocalHomeomorph, ?_⟩
  intro t ht x v w
  obtain ⟨r, _, he⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
    (R.round_at_all_times 0 le_rfl)
  have hscalar : (K.flow.connection 0).scalarCurvature (q x) =
      (K.flow.connection 0).scalarCurvature p := (he _).trans (he _).symm
  have hm : (K.flow.metric 0).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
      (mfderiv (𝓡 2) (𝓡 2) q x w) =
        (2 / (K.flow.connection 0).scalarCurvature p) * (roundSphereMetric 2).inner x v w := by
    apply (mul_left_cancel₀ hr.ne')
    rw [hmetric]
    field_simp
  rw [K.flow.inner_eq_terminal_scalar_scale_of_round R.round_at_all_times t ht,
    hscalar, hm]
  field_simp



theorem exists_calibrated_roundSphereFamily_cover
    (R : TwoDimensionalAncientRoundCertificate K) :
    ∃ c : ℝ, 0 < c ∧ ∃ (F : M27RoundSphereFamily) (q : UnitTwoSphere → M),
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧ IsCoveringMap q ∧
      (∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (K.flow.metric t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
          (mfderiv (𝓡 2) (𝓡 2) q x w) = (F.metric t).inner x v w) ∧
      ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (F.metric t).inner x v w = (c - 2 * t) * (roundSphereMetric 2).inner x v w := by
  classical
  let p : M := Classical.choice inferInstance
  have hc : 0 < 2 / (K.flow.connection 0).scalarCurvature p := by
    obtain ⟨c, hc, he⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
      (R.round_at_all_times 0 le_rfl)
    rw [he p]
    positivity
  obtain ⟨q, hq, hsurj, hlocal, hcover, hmetric⟩ :=
    R.exists_evolving_sphere_cover_at_terminal_scale p
  let gs := fun t => (K.flow.metric t).pullbackOfLocalDiffeomorph q hlocal
  have hround (t : ℝ) (ht : t ≤ 0) :
      ConstantPositiveSectionalCurvature (gs t) (gs t).leviCivitaData := by
    obtain ⟨c, hc, hcurv⟩ := R.round_at_all_times t ht
    refine ⟨c, hc, fun x v w hv hw hvw => ?_⟩
    rw [(gs t).leviCivitaData.sectionalCurvature_eq_of_local_isometry
      (K.flow.connection t) isOpen_univ hq.contMDiffOn
      (fun _ _ _ _ => rfl) (Set.mem_univ x)]
    exact hcurv (q x) _ _ hv hw hvw
  have hanti (t : ℝ) (ht : t ≤ 0) (x : UnitTwoSphere)
      (v w : TangentSpace (𝓡 2) x) :
      (gs t).inner (-x) (mfderiv (𝓡 2) (𝓡 2) (fun y : UnitTwoSphere => -y) x v)
        (mfderiv (𝓡 2) (𝓡 2) (fun y : UnitTwoSphere => -y) x w) =
          (gs t).inner x v w := by
    change (K.flow.metric t).inner (q (-x))
      (mfderiv (𝓡 2) (𝓡 2) q (-x)
        (mfderiv (𝓡 2) (𝓡 2) (fun y : UnitTwoSphere => -y) x v))
      (mfderiv (𝓡 2) (𝓡 2) q (-x)
        (mfderiv (𝓡 2) (𝓡 2) (fun y : UnitTwoSphere => -y) x w)) =
      (K.flow.metric t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
        (mfderiv (𝓡 2) (𝓡 2) q x w)
    rw [hmetric t ht, hmetric t ht]
    have hneg : (sphereMotion (LinearIsometryEquiv.neg ℝ) : UnitTwoSphere → UnitTwoSphere) =
        fun y => -y := rfl
    have hm := sphereMotion_inner (LinearIsometryEquiv.neg ℝ) x v w
    rw [hneg] at hm
    rw [hm]
  exact ⟨2 / (K.flow.connection 0).scalarCurvature p, hc, {
    metric := gs
    connection := fun t => (gs t).leviCivitaData
    round := hround
    antipodal_isometry := hanti
  }, q, hq, hsurj, hlocal, hcover, (fun _ _ _ _ _ => rfl), hmetric⟩


theorem exists_roundSphereFamily_cover
    (R : TwoDimensionalAncientRoundCertificate K) :
    ∃ (F : M27RoundSphereFamily) (q : UnitTwoSphere → M),
      ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧ IsCoveringMap q ∧
      ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (K.flow.metric t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
          (mfderiv (𝓡 2) (𝓡 2) q x w) = (F.metric t).inner x v w := by
  obtain ⟨_, _, F, q, hq, hs, hl, hc, hm, _⟩ := R.exists_calibrated_roundSphereFamily_cover
  exact ⟨F, q, hq, hs, hl, hc, hm⟩



theorem exists_calibrated_roundSphereFamily_diffeomorph [SimplyConnectedSpace M]
    (R : TwoDimensionalAncientRoundCertificate K) :
    ∃ c : ℝ, 0 < c ∧ ∃ (F : M27RoundSphereFamily) (q : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ M),
      (∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (K.flow.metric t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
          (mfderiv (𝓡 2) (𝓡 2) q x w) = (F.metric t).inner x v w) ∧
      ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (F.metric t).inner x v w = (c - 2 * t) * (roundSphereMetric 2).inner x v w := by
  obtain ⟨c, hc, F, q, _, _, hlocal, hcover, hmetric, hscale⟩ :=
    R.exists_calibrated_roundSphereFamily_cover
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  exact ⟨c, hc, F, hlocal.diffeomorphOfBijective
    (Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hcover), hmetric, hscale⟩



theorem exists_roundSphereFamily_diffeomorph [SimplyConnectedSpace M]
    (R : TwoDimensionalAncientRoundCertificate K) :
    ∃ (F : M27RoundSphereFamily) (q : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ M),
      ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
        (K.flow.metric t).inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
          (mfderiv (𝓡 2) (𝓡 2) q x w) = (F.metric t).inner x v w := by
  obtain ⟨_, _, F, q, hmetric, _⟩ := R.exists_calibrated_roundSphereFamily_diffeomorph
  exact ⟨F, q, hmetric⟩

end PoincareConjecture.TwoDimensionalAncientRoundCertificate
