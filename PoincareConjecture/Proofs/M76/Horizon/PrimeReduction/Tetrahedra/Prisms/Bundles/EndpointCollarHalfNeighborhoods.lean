import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarPathSides



set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt

theorem exists_connected_collar_half_neighborhoods
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    [LocallyPathConnectedSpace A] {K S O V : Set X}
    (W : (A × unitInterval) ≃ₜ K) (a : A)
    (hO : IsOpen O) (hV : IsOpen V)
    (hcenter : ∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (ha : (W (a,⟨1/2,by norm_num,by norm_num⟩) : X) ∈ V ∩ O) :
    ∃ (u : Set A) (lo hi : unitInterval),
      IsOpen u ∧ a ∈ u ∧ IsPathConnected u ∧
      (lo : ℝ) < 1/2 ∧ 1/2 < (hi : ℝ) ∧
      (∀ z ∈ u ×ˢ Ioo lo hi, (W z : X) ∈ V ∩ O) ∧
      ∀ b : Bool,
        let t := if b then Ioo (⟨1/2,by norm_num,by norm_num⟩ : unitInterval) hi
          else Ioo lo (⟨1/2,by norm_num,by norm_num⟩ : unitInterval)
        IsPreconnected ((fun z => (W z : X)) '' (u ×ˢ t)) ∧
        ((fun z => (W z : X)) '' (u ×ˢ t)) ⊆ (V ∩ O) \ S := by
  let m : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  have hopen : IsOpen ((fun z => (W z : X)) ⁻¹' (V ∩ O)) :=
    (hV.inter hO).preimage (continuous_subtype_val.comp W.continuous)
  obtain ⟨u₀,j,hu₀,hj,hau,hmj,hrect⟩ := isOpen_prod_iff.mp hopen a m ha
  obtain ⟨u,⟨hu,hau,hupath⟩,huu⟩ :=
    (isOpen_isPathConnected_basis a).mem_iff.mp (hu₀.mem_nhds hau)
  obtain ⟨lo,hi,hbounds,hinterval⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' (a := m)
      ⟨0,by change (0 : ℝ) < 1/2; norm_num⟩
      ⟨1,by change (1/2 : ℝ) < 1; norm_num⟩).mp (hj.mem_nhds hmj)
  have hrect' : ∀ z ∈ u ×ˢ Ioo lo hi, (W z : X) ∈ V ∩ O :=
    fun z hz => hrect ⟨huu hz.1,hinterval hz.2⟩
  refine ⟨u,lo,hi,hu,hau,hupath,hbounds.1,hbounds.2,hrect',?_⟩
  intro b
  have ht : IsPreconnected (if b then Ioo m hi else Ioo lo m) := by
    cases b <;> exact isPreconnected_Ioo
  refine ⟨(hupath.isConnected.isPreconnected.prod ht).image _
    (continuous_subtype_val.comp W.continuous).continuousOn,?_⟩
  rintro x ⟨z,hz,rfl⟩
  have hzi : z.2 ∈ Ioo lo hi := by
    cases b
    · exact ⟨hz.2.1,hz.2.2.trans hbounds.2⟩
    · exact ⟨hbounds.1.trans hz.2.1,hz.2.2⟩
  refine ⟨hrect' z ⟨hz.1,hzi⟩,?_⟩
  rw [hcenter]
  cases b
  · exact ne_of_lt hz.2.2
  · exact ne_of_gt hz.2.1

theorem exists_path_mem_collar_rectangle
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    {K O : Set X} (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K)
    {u : Set A} (hu : IsOpen u) {lo hi : unitInterval}
    (γ : C(unitInterval,X)) (z : A × unitInterval)
    (hz : z ∈ u ×ˢ Ioo lo hi) (hzero : γ 0 = W z) (hzeroO : γ 0 ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
      ∀ t : unitInterval, (t : ℝ) < ε →
        γ t ∈ (fun z => (W z : X)) '' (u ×ˢ Ioo lo hi) := by
  have hopen := W.isOpenMap (u ×ˢ Ioo lo hi) (hu.prod isOpen_Ioo)
  obtain ⟨v,hv,hveq⟩ := isOpen_induced_iff.mp hopen
  have hzeroV : γ 0 ∈ v := by
    rw [hzero]
    change W z ∈ Subtype.val ⁻¹' v
    rw [hveq]
    exact mem_image_of_mem W hz
  obtain ⟨r,hr,hrball⟩ := Metric.isOpen_iff.mp
    ((hO.inter hv).preimage γ.continuous) 0 ⟨hzeroO,hzeroV⟩
  refine ⟨min r (1/2),lt_min hr (by norm_num),min_le_right _ _,?_⟩
  intro t ht
  have htball : dist t (0 : unitInterval) < r := by
    change dist (t : ℝ) 0 < r
    rw [Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_le (min_le_left _ _)
  have htv := hrball htball
  have hmem : (⟨γ t,hOK htv.1⟩ : K) ∈ W '' (u ×ˢ Ioo lo hi) := by
    rw [← hveq]
    exact htv.2
  obtain ⟨w,hw,he⟩ := hmem
  exact ⟨w,hw,congrArg Subtype.val he⟩

theorem path_zero_mem_closure_of_initial_segment
    {X : Type*} [TopologicalSpace X] (γ : C(unitInterval,X))
    {C : Set X} {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hmem : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < ε → γ t ∈ C) :
    γ 0 ∈ closure C := by
  let e : unitInterval := ⟨ε,hε.le,hεone⟩
  have he : (0 : unitInterval) < e := hε
  have hzero : (0 : unitInterval) ∈ closure (Ioo 0 e) := by
    rw [closure_Ioo he.ne]
    exact ⟨le_rfl,he.le⟩
  exact (closure_mono (show γ '' Ioo 0 e ⊆ C by
    rintro _ ⟨t,ht,rfl⟩
    exact hmem t ht.1 ht.2))
    (image_closure_subset_closure_image γ.continuous
      (mem_image_of_mem γ hzero))

end PoincareConjecture.M76.PrismBelt
