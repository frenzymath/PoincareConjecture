import PoincareConjecture.Proofs.M47.CanonicalNeckAxialCompression
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckRestriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47


noncomputable def neckAxialInverse (lambda c : ℝ) (z : RoundCylinderSpace) : RoundCylinderSpace :=
  (z.1, (z.2 - c) / lambda)

theorem neckAxialInverse_contMDiff (lambda c : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (neckAxialInverse lambda c) := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => (s - c) / lambda) :=
    (contDiff_id.sub contDiff_const).div_const lambda
  exact contMDiff_fst.prodMk (h.contMDiff.comp contMDiff_snd)

theorem neckAxialInverse_left {lambda : ℝ} (hlambda : lambda ≠ 0)
    (c : ℝ) (z : RoundCylinderSpace) :
    neckAxialInverse lambda c (neckAxialSpaceMap lambda c z) = z := by
  apply Prod.ext
  · rfl
  · dsimp only [neckAxialInverse, neckAxialSpaceMap]
    field_simp
    ring

theorem neckAxialInverse_right {lambda : ℝ} (hlambda : lambda ≠ 0)
    (c : ℝ) (z : RoundCylinderSpace) :
    neckAxialSpaceMap lambda c (neckAxialInverse lambda c z) = z := by
  apply Prod.ext
  · rfl
  · dsimp only [neckAxialInverse, neckAxialSpaceMap]
    field_simp
    ring

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



def compressedNeckCarrier (N : EpsilonNeck g) (lambda c : ℝ) : Set M :=
  N.carrier ∩ (neckAxialInverse lambda c ∘ N.coordinate_inverse) ⁻¹'
    (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)

theorem compressedNeckCarrier_isOpen (N : EpsilonNeck g) (lambda c : ℝ) :
    IsOpen (compressedNeckCarrier N lambda c) := by
  have h : ContinuousOn (neckAxialInverse lambda c ∘ N.coordinate_inverse) N.carrier :=
    (neckAxialInverse_contMDiff lambda c).continuous.comp_continuousOn
      N.coordinate_inverse_smooth.continuousOn
  exact h.isOpen_inter_preimage N.carrier_open (isOpen_univ.prod isOpen_Ioo)



noncomputable def compressedNeckCoordinate (N : EpsilonNeck g)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹) :
    NeckDomain N.epsilon ≃ₜ compressedNeckCarrier N lambda c := by
  let inc : NeckDomain N.epsilon → NeckDomain N.epsilon := fun z =>
    (z.1, ⟨lambda * z.2 + c,
      neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hc
        ⟨z.2.property.1.le, z.2.property.2.le⟩⟩)
  have hinc : Continuous inc := continuous_fst.prodMk
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).add
      continuous_const |>.subtype_mk _)
  have hleft (z : NeckDomain N.epsilon) :
      neckAxialInverse lambda c (N.coordinate_inverse (N.coordinate (inc z))) =
        (z.1, (z.2 : ℝ)) := by
    rw [N.coordinate_inverse_left]
    exact neckAxialInverse_left hlambda.1.ne' c (z.1, z.2)
  have hmap (z : NeckDomain N.epsilon) :
      (N.coordinate (inc z) : M) ∈ compressedNeckCarrier N lambda c := by
    refine ⟨(N.coordinate (inc z)).property, ?_⟩
    change neckAxialInverse lambda c (N.coordinate_inverse (N.coordinate (inc z))) ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [hleft]
    exact ⟨mem_univ _, z.2.property⟩
  have hinvcont : Continuous (fun x : compressedNeckCarrier N lambda c =>
      neckAxialInverse lambda c (N.coordinate_inverse (x : M))) :=
    (neckAxialInverse_contMDiff lambda c).continuous.comp
      (N.coordinate_inverse_smooth.continuousOn.comp_continuous
        continuous_subtype_val (fun x => x.property.1))
  refine {
    toFun := fun z => ⟨N.coordinate (inc z), hmap z⟩
    invFun := fun x => ((neckAxialInverse lambda c (N.coordinate_inverse x)).1,
      ⟨(neckAxialInverse lambda c (N.coordinate_inverse x)).2, x.property.2.2⟩)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun :=
      (continuous_subtype_val.comp (N.coordinate.continuous.comp hinc)).subtype_mk _
    continuous_invFun := hinvcont.fst.prodMk (hinvcont.snd.subtype_mk _)
  }
  · intro z
    apply Prod.ext
    · exact congrArg (fun y : RoundCylinderSpace => y.1) (hleft z)
    · exact Subtype.ext (congrArg (fun y : RoundCylinderSpace => y.2) (hleft z))
  · intro x
    apply Subtype.ext
    rw [N.coordinate_map_eq]
    change N.coordinate_map (neckAxialSpaceMap lambda c
      (neckAxialInverse lambda c (N.coordinate_inverse x))) = x
    rw [neckAxialInverse_right hlambda.1.ne']
    have h := congrArg (fun y : N.carrier => (y : M))
      (N.coordinate_inverse_right x x.property.1)
    rw [N.coordinate_map_eq] at h
    exact h

theorem compressedNeckCoordinate_map_eq (N : EpsilonNeck g)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹) (z : NeckDomain N.epsilon) :
    (compressedNeckCoordinate N hlambda hc z : M) =
      N.coordinate_map (neckAxialSpaceMap lambda c (z.1, (z.2 : ℝ))) := by
  exact N.coordinate_map_eq _

theorem compressedNeckCoordinate_inverse_left (N : EpsilonNeck g)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹) (z : NeckDomain N.epsilon) :
    neckAxialInverse lambda c
        (N.coordinate_inverse (compressedNeckCoordinate N hlambda hc z)) =
      (z.1, (z.2 : ℝ)) := by
  rw [compressedNeckCoordinate_map_eq,
    N.coordinate_inverse_coordinate_map_of_axial_mem
      (neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hc
        ⟨z.2.property.1.le, z.2.property.2.le⟩)]
  exact neckAxialInverse_left hlambda.1.ne' c _



theorem compressedNeckCoordinate_map_smooth (N : EpsilonNeck g)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (N.coordinate_map ∘ neckAxialSpaceMap lambda c)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  apply N.coordinate_map_smooth.comp (neckAxialSpaceMap_contMDiff lambda c).contMDiffOn
  intro z hz
  exact ⟨mem_univ _, neckAxialCoordinate_mem_open_interval N.epsilon_pos hlambda hc
    ⟨hz.2.1.le, hz.2.2.le⟩⟩

theorem compressedNeckCoordinate_inverse_smooth (N : EpsilonNeck g)
    (lambda c : ℝ) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (neckAxialInverse lambda c ∘ N.coordinate_inverse)
      (compressedNeckCarrier N lambda c) := by
  exact (neckAxialInverse_contMDiff lambda c).comp_contMDiffOn
    (N.coordinate_inverse_smooth.mono inter_subset_left)

end PoincareConjecture.Proofs.M47
