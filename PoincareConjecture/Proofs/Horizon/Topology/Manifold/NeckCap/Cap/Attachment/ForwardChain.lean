import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ChainTail
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.EndSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Forward
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Certificate

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_forward_cap_chain_separating_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (T : BalancedNeckChain g C.epsilon) (a : ℤ),
          T.shape = .forward a → T.neck a = C.end_neck →
          ∀ j ∈ T.shape.active, (T.neck j).IsSeparating := by
  obtain ⟨ε₁, hε₁, hsmall, hsep⟩ := exists_end_neck_separating_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hagree⟩ := EpsilonNeck.exists_contained_slice_separation_agreement.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T a hshape hfirst
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hactive (n : ℕ) : a + (n : ℤ) ∈ T.shape.active := by
    rw [hshape]
    change a ≤ a + (n : ℤ)
    omega
  have hsepn (n : ℕ) : (T.neck (a + (n : ℤ))).IsSeparating := by
    induction n with
    | zero =>
      simpa only [Int.natCast_zero, add_zero, hfirst] using hsep C (hε.trans (min_le_left _ _))
    | succ n ih =>
      have hnext : a + (n : ℤ) + 1 ∈ T.shape.active := by
        simpa only [Int.natCast_add, Int.natCast_one, ← add_assoc] using hactive (n + 1)
      have hNε := T.epsilon_eq (a + (n : ℤ)) (hactive n)
      have hQε := T.epsilon_eq (a + (n : ℤ) + 1) hnext
      have hquarter := (T.overlap_contains_quarters _ (hactive n) hnext).2
      have hc : -(3 / 4 : ℝ) * C.epsilon⁻¹ ∈
          Ioo (-(T.neck (a + (n : ℤ) + 1)).epsilon⁻¹)
            (T.neck (a + (n : ℤ) + 1)).epsilon⁻¹ := by
        rw [hQε]
        constructor <;> linarith
      have hslice (q : UnitTwoSphere) :
          (T.neck (a + (n : ℤ) + 1)).coordinate_map
            (q, -(3 / 4 : ℝ) * C.epsilon⁻¹) ∈ (T.neck (a + (n : ℤ))).carrier := by
        apply hquarter
        refine ⟨(T.neck (a + (n : ℤ) + 1)).coordinate_map_mem ⟨mem_univ _, hc⟩, ?_⟩
        rw [(T.neck (a + (n : ℤ) + 1)).coordinate_inverse_coordinate_map ⟨mem_univ _, hc⟩]
        constructor <;> linarith
      have hs := (hagree (T.neck (a + (n : ℤ))) (T.neck (a + (n : ℤ) + 1))
        (hNε.trans_le (hε.trans (min_le_right _ _)))
        (hQε.trans_le (hε.trans (min_le_right _ _))) hc hslice).1.mpr ih
      simpa only [Int.natCast_add, Int.natCast_one, ← add_assoc] using hs
  intro j hj
  have haj : a ≤ j := by simpa only [hshape, ChainShape.active, mem_Ici] using hj
  have hindex : a + ((j - a).toNat : ℤ) = j := by omega
  simpa only [hindex] using hsepn (j - a).toNat

theorem exists_forward_capped_tube_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (T : BalancedNeckChain g C.epsilon) (a : ℤ),
          T.shape = .forward a → T.neck a = C.end_neck →
          (∀ j ∈ T.shape.active, a < j → (T.neck j).center ∉ C.carrier) →
          ∃ A : CappedTubeCertificate g, A.cap = C ∧
            A.tube.epsilon = C.epsilon ∧ HEq A.tube.chain T ∧
            A.carrier = C.carrier ∪ (T.unionOpen : Set M) := by
  obtain ⟨ε₁, hε₁, hsmall, hattach⟩ := exists_outgoing_chain_capTubeAttachment_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hsep⟩ := exists_forward_cap_chain_separating_threshold.{u}
  obtain ⟨ε₃, hε₃, -, hforward⟩ := BalancedNeckChain.exists_forward_cylinder_with_tail_threshold.{u}
  obtain ⟨ε₄, hε₄, -, hmodel⟩ := BalancedNeckChain.exists_openCylinderModel_of_middle_slice_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)), lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T a hshape hfirst hcenters
  have h₁ := hε.trans (min_le_left _ _)
  have hrest := hε.trans (min_le_right _ _)
  have h₂ := hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have h₃ := hrest.trans (min_le_left _ _)
  have h₄ := hrest.trans (min_le_right _ _)
  have ha : a ∈ T.shape.active := by
    simpa only [hshape, ChainShape.active, mem_Ici] using (le_refl a)
  have hleast : ∀ j ∈ T.shape.active, a ≤ j := by
    intro j hj
    simpa only [hshape, ChainShape.active, mem_Ici] using hj
  obtain ⟨D, _, -, -, hzero⟩ := hforward T h₃ (hsep C h₂ T a hshape hfirst) a hshape
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hc : -(3 / 4 : ℝ) * C.epsilon⁻¹ ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    constructor <;> linarith
  obtain ⟨model, hisotopy⟩ := hmodel T h₄ D a ha _ hc hzero
  let tube : EpsilonTubeCertificate g ∅ := T.tubeCertificateOfCylinder
    ((h₁.trans hsmall).trans (by norm_num)) model hisotopy ∅ (empty_subset _)
  obtain ⟨side, ⟨attachment⟩⟩ := hattach C h₁ T a ha hfirst hleast hcenters tube rfl
  have hend : C.end_neck.carrier ⊆ tube.carrier := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hfirst.symm ▸ hx⟩
  have hcenter : C.end_neck.center ∈ C.end_neck.carrier :=
    C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere
  let A : CappedTubeCertificate g :=
    { carrier := C.carrier ∪ tube.carrier
      cap := C
      tube := tube
      cap_subset := subset_union_left
      tube_subset := subset_union_right
      carrier_eq_union := rfl
      connected := C.isConnected_carrier.union
        ⟨C.end_neck.center, C.end_neck_subset hcenter, hend hcenter⟩
        tube.cylinder.isConnected_carrier
      attachment_side := side
      attachment := attachment }
  exact ⟨A, rfl, rfl, HEq.rfl, rfl⟩

end PoincareConjecture.CapCertificate
