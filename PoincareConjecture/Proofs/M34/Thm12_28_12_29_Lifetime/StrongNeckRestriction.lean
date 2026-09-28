import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckComparison
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem coordinate_inverse_coordinate_map_of_axial_mem {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_inverse (N.coordinate_map z) = z := by
  let z' : NeckDomain N.epsilon := (z.1, ⟨z.2, hz⟩)
  have h := N.coordinate_inverse_left z'
  rw [N.coordinate_map_eq] at h
  exact h



theorem coordinate_map_mem_of_axial_mem {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) : N.coordinate_map z ∈ N.carrier := by
  let z' : NeckDomain N.epsilon := (z.1, ⟨z.2, hz⟩)
  rw [← N.coordinate_map_eq z']
  exact (N.coordinate z').property



def restrictedCarrier (epsilon : ℝ) : Set M :=
  N.carrier ∩ N.coordinate_inverse ⁻¹' (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)



theorem restrictedCarrier_isOpen (epsilon : ℝ) : IsOpen (N.restrictedCarrier epsilon) :=
  N.coordinate_inverse_smooth.continuousOn.isOpen_inter_preimage N.carrier_open
    (isOpen_univ.prod isOpen_Ioo)


noncomputable def restrictedCoordinate {epsilon : ℝ} (h : N.epsilon ≤ epsilon) :
    NeckDomain epsilon ≃ₜ N.restrictedCarrier epsilon := by
  have hinv : epsilon⁻¹ ≤ N.epsilon⁻¹ := inv_anti₀ N.epsilon_pos h
  let inc : NeckDomain epsilon → NeckDomain N.epsilon := fun z =>
    (z.1, ⟨z.2, lt_of_le_of_lt (neg_le_neg hinv) z.2.property.1,
      z.2.property.2.trans_le hinv⟩)
  have hinc : Continuous inc :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hmap (z : NeckDomain epsilon) :
      (N.coordinate (inc z) : M) ∈ N.restrictedCarrier epsilon := by
    refine ⟨(N.coordinate (inc z)).property, mem_univ _, ?_⟩
    rw [N.coordinate_inverse_left]
    exact z.2.property
  have hinvcont : Continuous (fun x : N.restrictedCarrier epsilon =>
      N.coordinate_inverse (x : M)) :=
    N.coordinate_inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property.1)
  refine {
    toFun := fun z => ⟨N.coordinate (inc z), hmap z⟩
    invFun := fun x => ((N.coordinate_inverse x).1,
      ⟨(N.coordinate_inverse x).2, x.property.2.2⟩)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun :=
      (continuous_subtype_val.comp (N.coordinate.continuous.comp hinc)).subtype_mk _
    continuous_invFun := hinvcont.fst.prodMk (hinvcont.snd.subtype_mk _)
  }
  · intro z
    have hz := N.coordinate_inverse_left (inc z)
    apply Prod.ext
    · exact congrArg (fun y : RoundCylinderSpace => y.1) hz
    · apply Subtype.ext
      exact congrArg (fun y : RoundCylinderSpace => y.2) hz
  · intro x
    apply Subtype.ext
    exact congrArg (fun y : N.carrier => (y : M))
      (N.coordinate_inverse_right x x.property.1)



noncomputable def restrict {epsilon : ℝ} (h : N.epsilon ≤ epsilon)
    (hepsilon : epsilon < 1 / 2) : EpsilonNeck g where
  epsilon := epsilon
  epsilon_pos := N.epsilon_pos.trans_le h
  epsilon_lt_half := hepsilon
  scale := N.scale
  scale_pos := N.scale_pos
  center := N.center
  connection := N.connection
  scalar_center_pos := N.scalar_center_pos
  scale_eq_scalar := N.scale_eq_scalar
  carrier := N.restrictedCarrier epsilon
  carrier_open := N.restrictedCarrier_isOpen epsilon
  coordinate := N.restrictedCoordinate h
  coordinate_map := N.coordinate_map
  coordinate_map_eq := fun z => N.coordinate_map_eq _
  coordinate_map_smooth := N.coordinate_map_smooth.mono (by
    have hinv := inv_anti₀ N.epsilon_pos h
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt (neg_le_neg hinv) hz.2.1, hz.2.2.trans_le hinv⟩)
  coordinate_inverse := N.coordinate_inverse
  coordinate_inverse_mem := fun _ hx => hx.2
  coordinate_inverse_left := fun z => N.coordinate_inverse_left _
  coordinate_inverse_right := fun x hx => (N.restrictedCoordinate h).apply_symm_apply ⟨x, hx⟩
  coordinate_inverse_smooth := N.coordinate_inverse_smooth.mono inter_subset_left
  central_sphere := N.central_sphere
  central_sphere_eq := N.central_sphere_eq
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := by
    intro x hx
    refine ⟨N.central_sphere_subset hx, mem_univ _, ?_⟩
    obtain ⟨z, hz, rfl⟩ := N.central_sphere_eq ▸ hx
    have hz0 : z.2 = 0 := hz.2
    have hpos := inv_pos.mpr (N.epsilon_pos.trans_le h)
    rw [N.coordinate_inverse_coordinate_map_of_axial_mem (by
      rw [hz0]
      exact ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩), hz0]
    exact ⟨neg_neg_of_pos hpos, hpos⟩
  metric_comparison := ⟨N.metric_comparison.close.mono_epsilon N.epsilon_pos h (by norm_num)⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.StrongEvolvingNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {t delta : ℝ}



noncomputable def restrict (N : StrongEvolvingNeck K t delta)
    {epsilon : ℝ} (h : delta ≤ epsilon) (hepsilon : epsilon < 1 / 2) :
    StrongEvolvingNeck K t epsilon where
  time_mem := N.time_mem
  center := N.center
  duration := N.duration
  duration_pos := N.duration_pos
  normalized_duration := N.normalized_duration
  terminal_neck := N.terminal_neck.restrict (N.terminal_epsilon.trans_le h) hepsilon
  terminal_center := N.terminal_center
  terminal_epsilon := rfl
  terminal_connection := N.terminal_connection
  metric_comparison := N.metric_comparison.mono_epsilon
    (N.terminal_epsilon ▸ N.terminal_neck.epsilon_pos) h (fun _ hu => by linarith [hu.2])

end PoincareConjecture.StrongEvolvingNeck
