import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointPathLimit
import Mathlib.Topology.Connected.LocallyPathConnected








set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt

theorem exists_endpoint_of_finite_fiber_collar
    {A X Y : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {y : Y} (hfinite : (f ⁻¹' {y}).Finite)
    {γ : A × ℝ → X} {ε : ℝ} (hε : 0 < ε)
    (hγ : ContinuousOn γ (univ ×ˢ Ioo 0 ε)) (a : A)
    (hproj : Tendsto (f ∘ γ) (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 y)) :
    ∃ x : X, f x = y ∧ Tendsto γ (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 x) := by
  have hfiber {x : X} (hx : MapClusterPt x (𝓝 a ×ˢ 𝓝[>] 0) γ) : f x = y := by
    apply eq_of_nhds_neBot
    exact hx.map hf.continuousAt (by simpa only [Tendsto, map_map] using hproj)
  obtain ⟨x,hx⟩ := exists_clusterPt_of_compactSpace (map γ (𝓝 a ×ˢ 𝓝[>] (0 : ℝ)))
  refine ⟨x,hfiber hx,tendsto_nhds_of_unique_mapClusterPt fun z hz => ?_⟩
  apply eq_of_finite_fiber_common_connected_side hf hfinite (hfiber hz) (hfiber hx)
  intro V hV hyV
  obtain ⟨u₀,hu₀,v,hv,hrect⟩ := mem_prod_iff.mp (hproj (hV.mem_nhds hyV))
  obtain ⟨u,⟨hu,hau,hupath⟩,huu⟩ := (isOpen_isPathConnected_basis a).mem_iff.mp hu₀
  obtain ⟨δ,hδ,hδv⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hv
  let e := min ε δ
  have he : 0 < e := lt_min hε hδ
  have hrectangle : u ×ˢ Ioo 0 e ∈ 𝓝 a ×ˢ 𝓝[>] (0 : ℝ) :=
    prod_mem_prod (hu.mem_nhds hau) ((nhdsGT_basis 0).mem_of_mem he)
  have himage := Filter.image_mem_map (m := γ) hrectangle
  refine ⟨γ '' (u ×ˢ Ioo 0 e),
    (hupath.isConnected.isPreconnected.prod isPreconnected_Ioo).image γ
      (hγ.mono (prod_mono (subset_univ _) (Ioo_subset_Ioo_right (min_le_left _ _)))),
    ?_,hz.mem_closure_of_mem _ himage,hx.mem_closure_of_mem _ himage⟩
  rintro _ ⟨⟨b,t⟩,ht,rfl⟩
  exact hrect ⟨huu ht.1,hδv ⟨ht.2.1,ht.2.2.trans_le (min_le_right _ _)⟩⟩

theorem exists_continuous_finite_fiber_boundary_lift
    {A X Y : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (ψ : A → Y)
    (hfinite : ∀ a, (f ⁻¹' {ψ a}).Finite)
    {γ : A × ℝ → X} {ε : ℝ} (hε : 0 < ε)
    (hγ : ContinuousOn γ (univ ×ˢ Ioo 0 ε))
    (hproj : ∀ a, Tendsto (f ∘ γ) (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (ψ a))) :
    ∃ σ : C(A,X), (∀ a, f (σ a) = ψ a) ∧
      ∀ a, Tendsto γ (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (σ a)) := by
  choose σ hσ hlim using fun a =>
    exists_endpoint_of_finite_fiber_collar hf (hfinite a) hε hγ a (hproj a)
  have hcontinuous : Continuous σ := by
    apply continuous_iff_continuousAt.mpr
    intro a
    apply (closed_nhds_basis (σ a)).tendsto_right_iff.mpr
    intro V hV
    obtain ⟨u,hu,v,hv,hrect⟩ := mem_prod_iff.mp (hlim a hV.1)
    apply mem_of_superset hu
    intro b hb
    have hbLimit : Tendsto (fun t : ℝ => γ (b,t)) (𝓝[>] 0) (𝓝 (σ b)) :=
      (hlim b).comp (tendsto_const_nhds.prodMk tendsto_id)
    exact hV.2.mem_of_tendsto hbLimit (mem_of_superset hv (fun t ht => hrect ⟨hb,ht⟩))
  exact ⟨⟨σ,hcontinuous⟩,hσ,hlim⟩

theorem exists_continuous_core_inverse_boundary_lift
    {A X Y : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {D : Set X} {B : Set Y} {f : X → Y} (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (φ : C(A × ℝ,Y)) {ε : ℝ} (hε : 0 < ε)
    (hinto : ∀ a t, t ∈ Ioo 0 ε → φ (a,t) ∈ B)
    (hfinite : ∀ a, (f ⁻¹' {φ (a,0)}).Finite) :
    ∃ (σ : C(A,X)) (η : A × ℝ → X),
      (∀ a, f (σ a) = φ (a,0)) ∧
      (∀ a, Tendsto η (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (σ a))) ∧
      (∀ a t (ht : t ∈ Ioo 0 ε), η (a,t) = H.symm ⟨φ (a,t),hinto a t ht⟩) ∧
      ContinuousOn η (univ ×ˢ Ioo 0 ε) := by
  classical
  have hhalf : ε / 2 ∈ Ioo 0 ε := by constructor <;> linarith
  let η (z : A × ℝ) : X := if ht : z.2 ∈ Ioo 0 ε then
    H.symm ⟨φ z,hinto z.1 z.2 ht⟩ else H.symm ⟨φ (z.1,ε / 2),hinto _ _ hhalf⟩
  have hηval (a : A) (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      η (a,t) = H.symm ⟨φ (a,t),hinto a t ht⟩ := dif_pos ht
  have hη : ContinuousOn η (univ ×ˢ Ioo 0 ε) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h := continuous_subtype_val.comp (H.symm.continuous.comp
      ((φ.continuous.comp continuous_subtype_val).subtype_mk
        (fun z : (univ ×ˢ Ioo 0 ε : Set (A × ℝ)) => hinto _ _ z.property.2)))
    exact h.congr (fun z => (hηval z.1.1 z.1.2 z.property.2).symm)
  have hproj (a : A) : Tendsto (f ∘ η) (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (φ (a,0))) := by
    have hφ : Tendsto φ (𝓝 a ×ˢ 𝓝[>] 0) (𝓝 (φ (a,0))) :=
      (φ.continuous.tendsto (a,0)).mono_left (by
        rw [nhds_prod_eq]
        exact Filter.prod_mono le_rfl nhdsWithin_le_nhds)
    apply hφ.congr'
    filter_upwards [prod_mem_prod (univ_mem : (univ : Set A) ∈ 𝓝 a)
      ((nhdsGT_basis 0).mem_of_mem hε)] with z hz
    change φ z = f (η z)
    rw [show η z = H.symm ⟨φ z,hinto z.1 z.2 hz.2⟩ from hηval _ _ hz.2,
      hH,H.apply_symm_apply]
  obtain ⟨σ,hσ,hlim⟩ := exists_continuous_finite_fiber_boundary_lift hf
    (fun a => φ (a,0)) hfinite hε hη hproj
  exact ⟨σ,η,hσ,hlim,hηval,hη⟩

end PoincareConjecture.M76.PrismBelt
