import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarHalfNeighborhoods
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.FiniteFiberSideUniqueness

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem endpoint_eq_of_same_original_collar_side
    {X Y A : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {D : Set X} {B M S O K : Set Y} (f : X → Y) (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K) (a : A)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M)
    (hcenter : ∀ z, (W z : Y) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (haO : (W (a,⟨1/2,by norm_num,by norm_num⟩) : Y) ∈ O)
    (y₀ : Y) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (η : Bool → C(unitInterval,X))
    (hstart : ∀ b, f (η b 0) = W (a,⟨1/2,by norm_num,by norm_num⟩))
    (hfinite : (f ⁻¹' {f (η false 0)}).Finite)
    (hinto : ∀ b (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1/2 →
      η b t ∈ D ∧ f (η b t) ∈ connectedComponentIn (M \ S) y₀)
    (ε : ℝ) (hε : 0 < ε) (positive : Bool)
    (hside : ∀ b (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < ε →
      ∀ z : A × unitInterval, (W z : Y) = f (η b t) →
        if positive then 1/2 < (z.2 : ℝ) else (z.2 : ℝ) < 1/2) :
    η false 0 = η true 0 := by
  apply eq_of_finite_fiber_common_connected_side hf hfinite rfl
    ((hstart true).trans (hstart false).symm)
  intro V hV hVpoint
  let m : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  have haV : (W (a,m) : Y) ∈ V := (hstart false) ▸ hVpoint
  obtain ⟨u,lo,hi,hu,hau,hupath,hlo,hhi,hrect,hhalves⟩ :=
    exists_connected_collar_half_neighborhoods W a hO hV hcenter ⟨haV,haO⟩
  let γ (b : Bool) : C(unitInterval,Y) := ⟨fun t => f (η b t),hf.comp (η b).continuous⟩
  have hrectpath (b : Bool) := exists_path_mem_collar_rectangle W hO hOK hu (γ b) (a,m)
    ⟨hau,hlo,hhi⟩ (hstart b) (by change f (η b 0) ∈ O; rw [hstart]; exact haO)
  choose δ hδ hδhalf hδrect using hrectpath
  let e := min ε (min (δ false) (δ true))
  have he : 0 < e := lt_min hε (lt_min (hδ false) (hδ true))
  have heε : e ≤ ε := min_le_left _ _
  have heδ (b : Bool) : e ≤ δ b := by
    cases b
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hehalf : e ≤ 1/2 := (heδ false).trans (hδhalf false)
  let C : Set Y := (fun z => (W z : Y)) ''
    (u ×ˢ (if positive then Ioo m hi else Ioo lo m))
  have hC : IsPreconnected C := (hhalves positive).1
  have hCV : C ⊆ V := fun _ hx => ((hhalves positive).2 hx).1.1
  have hCM : C ⊆ M \ S := fun _ hx =>
    ⟨hOM ((hhalves positive).2 hx).1.2,((hhalves positive).2 hx).2⟩
  have hpathC (b : Bool) (t : unitInterval) (ht : 0 < (t : ℝ)) (hte : (t : ℝ) < e) :
      f (η b t) ∈ C := by
    obtain ⟨z,hz,hzvalue⟩ := hδrect b t (hte.trans_le (heδ b))
    refine ⟨z,⟨hz.1,?_⟩,hzvalue⟩
    have hs := hside b t ht (hte.trans_le heε) z hzvalue
    cases positive
    · exact ⟨hz.2.1,hs⟩
    · exact ⟨hs,hz.2.2⟩
  let t₀ : unitInterval := ⟨e/2,by linarith,by linarith⟩
  have ht₀pos : 0 < (t₀ : ℝ) := by change 0 < e/2; linarith
  have ht₀e : (t₀ : ℝ) < e := by change e/2 < e; linarith
  have hCcomponent : C ⊆ connectedComponentIn (M \ S) y₀ := by
    have hsub := hC.subset_connectedComponentIn (hpathC false t₀ ht₀pos ht₀e) hCM
    rwa [← connectedComponentIn_eq (hinto false t₀ ht₀pos (ht₀e.trans_le hehalf)).2] at hsub
  have hCB : C ⊆ B := hCcomponent.trans hcover
  let L : Set X := (fun z : B => (H.symm z : X)) '' (Subtype.val ⁻¹' C)
  have hCBpre : IsPreconnected (Subtype.val ⁻¹' C : Set B) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe,inter_eq_right.mpr hCB] using hC
  have hL : IsPreconnected L := hCBpre.image _
    (continuous_subtype_val.comp H.symm.continuous).continuousOn
  have hLV : L ⊆ f ⁻¹' V := by
    rintro x ⟨z,hz,rfl⟩
    change f (H.symm z) ∈ V
    rw [hH,H.apply_symm_apply]
    exact hCV hz
  have hpathL (b : Bool) (t : unitInterval) (ht : 0 < (t : ℝ)) (hte : (t : ℝ) < e) :
      η b t ∈ L := by
    have htD := (hinto b t ht (hte.trans_le hehalf)).1
    refine ⟨H ⟨η b t,htD⟩,?_,?_⟩
    · change (H ⟨η b t,htD⟩ : Y) ∈ C
      rw [← hH]
      exact hpathC b t ht hte
    · exact congrArg Subtype.val (H.symm_apply_apply _)
  exact ⟨L,hL,hLV,
    path_zero_mem_closure_of_initial_segment (η false) he (hehalf.trans (by norm_num)) (hpathL false),
    path_zero_mem_closure_of_initial_segment (η true) he (hehalf.trans (by norm_num)) (hpathL true)⟩

end PoincareConjecture.M76.PrismBelt
