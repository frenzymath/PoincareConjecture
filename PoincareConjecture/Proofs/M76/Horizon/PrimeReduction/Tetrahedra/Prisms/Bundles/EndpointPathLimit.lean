import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.FiniteFiberSideUniqueness
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt

theorem exists_endpoint_of_finite_fiber_path
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {y : Y} (hfinite : (f ⁻¹' {y}).Finite)
    {γ : ℝ → X} {ε : ℝ} (hε : 0 < ε) (hγ : ContinuousOn γ (Ioo 0 ε))
    (hproj : Tendsto (f ∘ γ) (𝓝[>] 0) (𝓝 y)) :
    ∃ x : X, f x = y ∧ Tendsto γ (𝓝[>] 0) (𝓝 x) := by
  have hfiber {x : X} (hx : MapClusterPt x (𝓝[>] 0) γ) : f x = y := by
    apply eq_of_nhds_neBot
    exact hx.map hf.continuousAt (by simpa only [Tendsto, map_map] using hproj)
  obtain ⟨x,hx⟩ := exists_clusterPt_of_compactSpace (map γ (𝓝[>] (0 : ℝ)))
  refine ⟨x,hfiber hx,tendsto_nhds_of_unique_mapClusterPt fun z hz => ?_⟩
  apply eq_of_finite_fiber_common_connected_side hf hfinite (hfiber hz) (hfiber hx)
  intro V hV hyV
  obtain ⟨δ,hδ,hδV⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hproj (hV.mem_nhds hyV))
  let e := min ε δ
  have he : 0 < e := lt_min hε hδ
  have hsegment : Ioo 0 e ∈ 𝓝[>] (0 : ℝ) := (nhdsGT_basis 0).mem_of_mem he
  have himage : γ '' Ioo 0 e ∈ map γ (𝓝[>] (0 : ℝ)) :=
    Filter.image_mem_map hsegment
  refine ⟨γ '' Ioo 0 e,
    isPreconnected_Ioo.image γ (hγ.mono (Ioo_subset_Ioo_right (min_le_left _ _))),
    ?_,hz.mem_closure_of_mem _ himage,hx.mem_closure_of_mem _ himage⟩
  rintro _ ⟨t,ht,rfl⟩
  exact hδV ⟨ht.1,ht.2.trans_le (min_le_right _ _)⟩

theorem exists_endpoint_of_core_inverse_path
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {D : Set X} {B : Set Y} {f : X → Y} (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    {γ : ℝ → Y} {ε : ℝ} (hε : 0 < ε)
    (hγ : ContinuousOn γ (Ioo 0 ε)) (hγ0 : ContinuousAt γ 0)
    (hinto : ∀ t ∈ Ioo 0 ε, γ t ∈ B)
    (hfinite : (f ⁻¹' {γ 0}).Finite) :
    ∃ (x : X) (η : ℝ → X), f x = γ 0 ∧ Tendsto η (𝓝[>] 0) (𝓝 x) ∧
      ∀ t (ht : t ∈ Ioo 0 ε), η t = H.symm ⟨γ t,hinto t ht⟩ := by
  classical
  have hhalf : ε / 2 ∈ Ioo 0 ε := by constructor <;> linarith
  let x₀ : X := H.symm ⟨γ (ε / 2),hinto _ hhalf⟩
  let η (t : ℝ) : X := if ht : t ∈ Ioo 0 ε then
    H.symm ⟨γ t,hinto t ht⟩ else x₀
  have hηval (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      η t = H.symm ⟨γ t,hinto t ht⟩ := dif_pos ht
  have hη : ContinuousOn η (Ioo 0 ε) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h := continuous_subtype_val.comp (H.symm.continuous.comp
      (hγ.domRestrict.subtype_mk (fun t => hinto t t.property)))
    exact h.congr (fun t => (hηval t t.property).symm)
  have hproj : Tendsto (f ∘ η) (𝓝[>] 0) (𝓝 (γ 0)) := by
    apply (hγ0.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [(nhdsGT_basis 0).mem_of_mem hε] with t ht
    change γ t = f (η t)
    rw [hηval t ht,hH,H.apply_symm_apply]
  obtain ⟨x,hx,hηx⟩ := exists_endpoint_of_finite_fiber_path hf hfinite hε hη hproj
  exact ⟨x,η,hx,hηx,hηval⟩

end PoincareConjecture.M76.PrismBelt
