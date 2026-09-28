import PoincareConjecture.Proofs.M34.Mathlib.CapPersistenceAxialCompression
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceAxialMap
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceModelTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

noncomputable def recutDiffeomorph {c b : ℝ}
    (hc : -N.epsilon⁻¹ < c) (hcb : c < b) (hb : b < N.epsilon⁻¹)
    (e : ℝ ≃o ℝ) (he : ContDiff ℝ ∞ (e : ℝ → ℝ))
    (he' : ContDiff ℝ ∞ (e.symm : ℝ → ℝ))
    (houter : e N.epsilon⁻¹ = b) (hfix : ∀ s ≤ c, e s = s) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞ := by
  have hinner : e (-N.epsilon⁻¹) = -N.epsilon⁻¹ := hfix _ hc.le
  have hinner' : e.symm (-N.epsilon⁻¹) = -N.epsilon⁻¹ := by
    apply e.injective
    rw [e.apply_symm_apply, hinner]
  have houter' : e.symm b = N.epsilon⁻¹ := by
    rw [← houter, e.symm_apply_apply]
  have hfix' : ∀ s ≤ c, e.symm s = s := by
    intro s hs
    apply e.injective
    rw [e.apply_symm_apply, hfix s hs]
  have hold {x : M} (hx : x ∈ N.end_neck.carrier) :
      e (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) b := by
    have ht : (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      simpa only [N.end_neck_epsilon] using (N.end_neck.coordinate_inverse_mem x hx).2
    exact ⟨hinner ▸ e.strictMono ht.1, houter ▸ e.strictMono ht.2⟩
  have hnew {x : M} (hx : x ∈ N.recutCarrier b) (heX : x ∈ N.end_neck.carrier) :
      e.symm (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have hxR : x ∈ N.end_neck.region (-N.epsilon⁻¹) b := by
      rcases hx with hx | hx
      · rw [N.closed_core_eq_complement_end] at hx
        exact False.elim (hx.2 heX)
      · exact hx
    exact ⟨hinner' ▸ e.symm.strictMono hxR.2.1, houter' ▸ e.symm.strictMono hxR.2.2⟩
  have hvalid {x : M} (hx : x ∈ N.end_neck.carrier) :
      e (N.end_neck.coordinate_inverse x).2 ∈
        Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    exact ⟨(hold hx).1, (hold hx).2.trans hb⟩
  have hvalid' {x : M} (hx : x ∈ N.recutCarrier b) (heX : x ∈ N.end_neck.carrier) :
      e.symm (N.end_neck.coordinate_inverse x).2 ∈
        Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    exact hnew hx heX
  refine {
    toFun := N.axialMap e
    invFun := N.axialMap e.symm
    source := N.carrier
    target := N.recutCarrier b
    open_source := N.carrier_open
    open_target := N.recutCarrier_isOpen (hc.trans hcb) hb
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    contMDiffOn_toFun := N.axialMap_contMDiffOn hc (hcb.trans hb) (Subset.refl _)
      he hfix (fun _ _ hx => ⟨(hold hx).1, (hold hx).2.trans hb⟩)
    contMDiffOn_invFun := N.axialMap_contMDiffOn hc (hcb.trans hb)
      (N.recutCarrier_subset_carrier b) he' hfix' (fun _ hx heX => hnew hx heX)
  }
  · intro x hx
    by_cases heX : x ∈ N.end_neck.carrier
    · simp only [axialMap, if_pos heX]
      refine Or.inr ⟨N.end_neck.coordinate_map_mem_of_axial_mem (hvalid heX), ?_⟩
      rw [N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem (hvalid heX)]
      exact hold heX
    · simp only [axialMap, if_neg heX]
      exact Or.inl (N.closed_core_eq_complement_end ▸ ⟨hx, heX⟩)
  · intro x hx
    by_cases heX : x ∈ N.end_neck.carrier
    · simp only [axialMap, if_pos heX]
      exact N.end_neck_subset (N.end_neck.coordinate_map_mem_of_axial_mem (hvalid' hx heX))
    · simpa only [axialMap, if_neg heX] using N.recutCarrier_subset_carrier b hx
  · intro x _hx
    by_cases heX : x ∈ N.end_neck.carrier
    · have him : N.end_neck.coordinate_map ((N.end_neck.coordinate_inverse x).1,
          e (N.end_neck.coordinate_inverse x).2) ∈ N.end_neck.carrier :=
        N.end_neck.coordinate_map_mem_of_axial_mem (hvalid heX)
      have heq : N.axialMap e x = N.end_neck.coordinate_map
          ((N.end_neck.coordinate_inverse x).1, e (N.end_neck.coordinate_inverse x).2) := by
        simp only [axialMap, if_pos heX]
      rw [heq, axialMap, if_pos him,
        N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem (hvalid heX)]
      simpa only [OrderIso.symm_apply_apply] using
        N.end_neck.coordinate_map_coordinate_inverse heX
    · have hfixed (f : ℝ → ℝ) : N.axialMap f x = x := by
        simp only [axialMap, if_neg heX]
      exact (congrArg (N.axialMap e.symm) (hfixed e)).trans (hfixed e.symm)
  · intro x hx
    by_cases heX : x ∈ N.end_neck.carrier
    · have him : N.end_neck.coordinate_map ((N.end_neck.coordinate_inverse x).1,
          e.symm (N.end_neck.coordinate_inverse x).2) ∈ N.end_neck.carrier :=
        N.end_neck.coordinate_map_mem_of_axial_mem (hvalid' hx heX)
      have heq : N.axialMap e.symm x = N.end_neck.coordinate_map
          ((N.end_neck.coordinate_inverse x).1, e.symm (N.end_neck.coordinate_inverse x).2) := by
        simp only [axialMap, if_pos heX]
      rw [heq, axialMap, if_pos him,
        N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem (hvalid' hx heX)]
      simpa only [OrderIso.apply_symm_apply] using
        N.end_neck.coordinate_map_coordinate_inverse heX
    · have hfixed (f : ℝ → ℝ) : N.axialMap f x = x := by
        simp only [axialMap, if_neg heX]
      exact (congrArg (N.axialMap e) (hfixed e.symm)).trans (hfixed e)

theorem nonempty_recutModelEquivalence {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    Nonempty (CapModelEquivalence N.model_kind N.puncture (N.recutCarrier b)) := by
  let c := (-N.epsilon⁻¹ + b) / 2
  have hc : -N.epsilon⁻¹ < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  obtain ⟨e, he, he', houter, hfix, _hderiv⟩ :=
    Real.exists_smooth_orderIso_compression hcb hb'
  let d := N.recutDiffeomorph hc hcb hb' e he he' houter hfix
  exact ⟨CapModelEquivalence.transport d N.model_equivalence⟩

end PoincareConjecture.CapCertificate
