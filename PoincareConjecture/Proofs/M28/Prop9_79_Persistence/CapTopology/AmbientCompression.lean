import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckAxialMap
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.OpenRecut
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.ModelTransport
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.AxialCompression












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in


theorem axialMap_eqOn_inner_recut (N : CapCertificate g) {β : ℝ → ℝ}
    (hfix : ∀ s, s ≤ 0 → β s = s) :
    EqOn (N.end_neck.axialMap β) id
      (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) 0) := by
  intro x hx
  rcases hx with hxY | hxE
  · exact N.end_neck.axialMap_of_not_mem β (N.closed_core_eq_complement_end ▸ hxY).2
  · rw [N.end_neck.axialMap_of_mem β hxE.1, hfix _ hxE.2.2.le]
    exact N.end_neck.coordinate_map_coordinate_inverse hxE.1



theorem contMDiffAt_axialMap_closed_core (N : CapCertificate g) {β : ℝ → ℝ}
    (hfix : ∀ s, s ≤ 0 → β s = s) {x : M} (hx : x ∈ N.closed_core) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.end_neck.axialMap β) x := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hW := N.isOpen_recut (q := 0) (by linarith) hA
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds (Or.inl hx)] with y hy
  exact N.axialMap_eqOn_inner_recut hfix hy




noncomputable def recutDiffeomorph_m28 (N : CapCertificate g) {b : ℝ}
    (hb : 0 < b) (hbA : b < N.epsilon⁻¹) (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (himage : e '' Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ = Ioo (-N.epsilon⁻¹) b)
    (hfix : ∀ s, s ≤ 0 → e s = s) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞ := by
  classical
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hmap : MapsTo e (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (Ioo (-N.epsilon⁻¹) b) :=
    fun _ hs => himage ▸ mem_image_of_mem e hs
  have hback : MapsTo e.symm (Ioo (-N.epsilon⁻¹) b) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
    intro s hs
    rw [← himage] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    simpa only [e.symm_apply_apply] using ht
  have hfixinv (s : ℝ) (hs : s ≤ 0) : e.symm s = s := by
    apply e.injective
    rw [e.apply_symm_apply, hfix s hs]
  have hheight (x : M) (hx : x ∈ N.end_neck.carrier) :
      (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [N.end_neck_epsilon] using (N.end_neck.coordinate_inverse_mem x hx).2
  have hforward (x : M) (hx : x ∈ N.end_neck.carrier) :
      e (N.end_neck.coordinate_inverse x).2 ∈
        Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    have h := hmap (hheight x hx)
    simpa only [N.end_neck_epsilon, mem_Ioo] using And.intro h.1 (h.2.trans hbA)
  have htarget_height (x : M)
      (hx : x ∈ N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b)
      (hxE : x ∈ N.end_neck.carrier) :
      (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) b := by
    rcases hx with hxY | hxR
    · exact False.elim ((N.closed_core_eq_complement_end ▸ hxY).2 hxE)
    · exact hxR.2
  have hinverse (x : M)
      (hx : x ∈ N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b)
      (hxE : x ∈ N.end_neck.carrier) :
      e.symm (N.end_neck.coordinate_inverse x).2 ∈
        Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    simpa only [N.end_neck_epsilon] using hback (htarget_height x hx hxE)
  have htargetV : N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b ⊆ N.carrier := by
    rintro x (hxY | hxE)
    · exact (N.closed_core_eq_complement_end ▸ hxY).1
    · exact N.end_neck_subset hxE.1
  refine {
    toFun := N.end_neck.axialMap e
    invFun := N.end_neck.axialMap e.symm
    source := N.carrier
    target := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := N.carrier_open
    open_target := N.isOpen_recut (by linarith) hbA
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · intro x hx
    by_cases hxE : x ∈ N.end_neck.carrier
    · right
      exact N.end_neck.axialMap_mem_region e hxE
        (by simp only [N.end_neck_epsilon, le_refl])
        (by simpa only [N.end_neck_epsilon] using hbA.le) (hmap (hheight x hxE))
    · rw [N.end_neck.axialMap_of_not_mem e hxE]
      left
      exact N.closed_core_eq_complement_end.symm ▸ And.intro hx hxE
  · intro x hx
    by_cases hxE : x ∈ N.end_neck.carrier
    · exact N.end_neck_subset
        (N.end_neck.axialMap_mem_region e.symm hxE le_rfl le_rfl (hinverse x hx hxE)).1
    · rw [N.end_neck.axialMap_of_not_mem e.symm hxE]
      exact htargetV hx
  · intro x _
    by_cases hxE : x ∈ N.end_neck.carrier
    · exact N.end_neck.axialMap_comp_eq e e.symm hxE (hforward x hxE)
        (e.symm_apply_apply _)
    · rw [N.end_neck.axialMap_of_not_mem e hxE,
        N.end_neck.axialMap_of_not_mem e.symm hxE]
  · intro x hx
    by_cases hxE : x ∈ N.end_neck.carrier
    · exact N.end_neck.axialMap_comp_eq e.symm e hxE (hinverse x hx hxE)
        (e.apply_symm_apply _)
    · rw [N.end_neck.axialMap_of_not_mem e.symm hxE,
        N.end_neck.axialMap_of_not_mem e hxE]
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hxE : x ∈ N.end_neck.carrier
    · exact N.end_neck.contMDiffAt_axialMap he hxE (hforward x hxE)
    · exact N.contMDiffAt_axialMap_closed_core hfix
        (N.closed_core_eq_complement_end.symm ▸ And.intro hx hxE)
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hxE : x ∈ N.end_neck.carrier
    · exact N.end_neck.contMDiffAt_axialMap hei hxE (hinverse x hx hxE)
    · exact N.contMDiffAt_axialMap_closed_core hfixinv
        (N.closed_core_eq_complement_end.symm ▸ And.intro (htargetV hx) hxE)



noncomputable def recutModelEquivalence (N : CapCertificate g) {b : ℝ}
    (hb : 0 < b) (hbA : b < N.epsilon⁻¹) (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (himage : e '' Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ = Ioo (-N.epsilon⁻¹) b)
    (hfix : ∀ s, s ≤ 0 → e s = s) :
    CapModelEquivalence N.model_kind N.puncture
      (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b) :=
  N.model_equivalence.transport_m28 (N.recutDiffeomorph_m28 hb hbA e he hei himage hfix) rfl




theorem eventually_exists_smooth_precompact_recut (N : CapCertificate g)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ᶠ k in atTop, 0 < δ k) :
    ∀ᶠ k in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞,
      e.source = N.carrier ∧
      e.target = N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) (N.epsilon⁻¹ - δ k) ∧
      IsCompact (closure e.target) ∧ closure e.target ⊆ N.carrier ∧
      (∀ x ∈ N.closed_core, e x = x) ∧
      e N.end_neck.center = N.end_neck.center ∧
      (∀ x ∈ N.end_neck.carrier, e x = N.end_neck.coordinate_map
        ((N.end_neck.coordinate_inverse x).1,
          (N.end_neck.coordinate_inverse x).2 - δ k *
            CapRecut.axialCutoff N.epsilon⁻¹ (inv_pos.mpr N.epsilon_pos)
              (N.end_neck.coordinate_inverse x).2)) ∧
      Nonempty (CapModelEquivalence N.model_kind N.puncture e.target) := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  filter_upwards [CapRecut.eventually_exists_axial_compression hA hδ hδpos] with k hk
  obtain ⟨hbhalf, hbA, α, hα, hαi, _, hformula, hfix, himage⟩ := hk
  have hb : 0 < N.epsilon⁻¹ - δ k := by linarith
  have hfixzero (s : ℝ) (hs : s ≤ 0) : α s = s := hfix s (by linarith)
  let e := N.recutDiffeomorph_m28 hb hbA α hα hαi himage hfixzero
  have hc := N.compact_closure_recut (b := N.epsilon⁻¹ - δ k) (by linarith) hbA
  refine ⟨e, rfl, rfl, hc.1, hc.2, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact N.end_neck.axialMap_of_not_mem α (N.closed_core_eq_complement_end ▸ hx).2
  · have hx := N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere
    apply N.end_neck.axialMap_eq_self_of_fixed_height α hx
    rw [(N.end_neck.mem_central_sphere_iff_of_mem_carrier hx).mp
      N.end_neck.center_on_central_sphere]
    exact hfixzero 0 le_rfl
  · intro x hx
    change N.end_neck.axialMap α x = _
    rw [N.end_neck.axialMap_of_mem α hx, hformula]
  · exact ⟨N.recutModelEquivalence hb hbA α hα hαi himage hfixzero⟩

end PoincareConjecture.CapCertificate
