import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCollarSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointLocalInjectivity
import Mathlib.Topology.IsLocalHomeomorph



set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt

theorem exists_endpoint_component_localHomeomorph
    {X Y A : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    {D : Set X} {B M S O K : Set Y} (f : X → Y) (hf : Continuous f)
    (H : D ≃ₜ B) (hH : ∀ x : D, f x = H x)
    (W : (A × unitInterval) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hOM : O ⊆ M) (hSO : S ⊆ O)
    (hcenter : ∀ z, (W z : Y) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (y₀ : Y) (hcover : connectedComponentIn (M \ S) y₀ ⊆ B)
    (hfinite : ∀ a, (f ⁻¹' {(W (a,⟨1/2,by norm_num,by norm_num⟩) : Y)}).Finite)
    (x₀ : X)
    (Γ : C(connectedComponentIn (f ⁻¹' S) x₀ × unitInterval,X))
    (hΓzero : ∀ p, Γ (p,0) = p)
    (hinto : ∀ p (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (p,t) ∈ D ∧ f (Γ (p,t)) ∈ connectedComponentIn (M \ S) y₀) :
    ∃ π : C(connectedComponentIn (f ⁻¹' S) x₀,S),
      (∀ p, (π p : Y) = f p) ∧
      IsLocalHomeomorph π := by
  let P := connectedComponentIn (f ⁻¹' S) x₀
  let m : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  have hP (p : P) : f p ∈ S := connectedComponentIn_subset (f ⁻¹' S) x₀ p.property
  let v (p : P) : K := ⟨f p,hOK (hSO (hP p))⟩
  let π : C(P,A) := ⟨fun p => (W.symm (v p)).1,
    continuous_fst.comp (W.symm.continuous.comp ((hf.comp continuous_subtype_val).subtype_mk _))⟩
  have hπ (p : P) : (W (π p,m) : Y) = f p := by
    have hz : (W.symm (v p)).2 = m := by
      apply Subtype.ext
      apply (hcenter _).mp
      simpa only [W.apply_symm_apply] using hP p
    change (W ((W.symm (v p)).1,m) : Y) = f p
    rw [← hz]
    exact congrArg Subtype.val (W.apply_symm_apply (v p))
  have hcenterO (a : A) : (W (a,m) : Y) ∈ O := hSO ((hcenter _).mpr rfl)
  have hzero (p : P) : f (Γ (p,0)) ∈ S := by rw [hΓzero]; exact hP p
  have hfiniteP (p : P) : (f ⁻¹' {f (Γ (p,0))}).Finite := by
    rw [hΓzero,← hπ]
    exact hfinite (π p)
  have hΓinj : Function.Injective (fun p : P => Γ (p,0)) := by
    intro p q he
    change Γ (p,0) = Γ (q,0) at he
    rw [hΓzero,hΓzero] at he
    exact Subtype.ext he
  have hlocal (p : P) : ∃ V : Set P, IsOpen V ∧ p ∈ V ∧ InjOn π V := by
    obtain ⟨V,hV,hpV,hinj⟩ := exists_endpoint_projection_injective_neighborhood
      f hf H hH W hO hOK hOM hcenter y₀ hcover Γ hzero hfiniteP hinto hΓinj p
      (hSO (hzero p))
    refine ⟨V,hV,hpV,?_⟩
    intro q hq z hz he
    apply hinj hq hz
    change f (Γ (q,0)) = f (Γ (z,0))
    rw [hΓzero,hΓzero,← hπ q,← hπ z,he]
  have hopen : IsOpenMap π := by
    intro N hN
    apply isOpen_iff_mem_nhds.mpr
    rintro a ⟨p,hp,rfl⟩
    let γ : C(unitInterval,X) :=
      ⟨fun t => Γ (p,t),Γ.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hγzero : γ 0 = (p : X) := hΓzero p
    have hstart : f (γ 0) = W (π p,m) := by rw [hγzero,hπ]
    obtain ⟨u,hu,hau,σ,hthrough,hσ,_hpath⟩ := exists_collar_section_through_endpoint
      f hf H hH W (π p) hO hOK hOM hcenter hcenterO y₀ hcover γ hstart hfinite (hinto p)
    have hcomponent : connectedComponentIn (f ⁻¹' S) (γ 0) = P := by
      rw [hγzero]
      exact (connectedComponentIn_eq p.property).symm
    let σ' : C(u,P) := ⟨fun b => ⟨σ b,hcomponent.subset (σ b).property⟩,
      (continuous_subtype_val.comp σ.continuous).subtype_mk _⟩
    have hthrough' : σ' ⟨π p,hau⟩ = p := Subtype.ext (hthrough.trans hγzero)
    have hsection (b : u) : π (σ' b) = (b : A) := by
      have hh : W (π (σ' b),m) = W (b,m) :=
        Subtype.ext ((hπ (σ' b)).trans (hσ b))
      exact congrArg Prod.fst (W.injective hh)
    have htarget : IsOpen (Subtype.val '' (σ' ⁻¹' N)) :=
      hu.isOpenMap_subtype_val _ (hN.preimage σ'.continuous)
    have hmember : π p ∈ Subtype.val '' (σ' ⁻¹' N) :=
      ⟨⟨π p,hau⟩,by change σ' ⟨π p,hau⟩ ∈ N; rw [hthrough']; exact hp,rfl⟩
    apply mem_of_superset (htarget.mem_nhds hmember)
    rintro _ ⟨b,hb,rfl⟩
    exact ⟨σ' b,hb,hsection b⟩
  have hlocalπ : IsLocalHomeomorph π := by
    apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
    intro p
    obtain ⟨V,hV,hp,hinj⟩ := hlocal p
    exact ⟨V,hV.mem_nhds hp,Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (π.continuous.comp continuous_subtype_val) (injOn_iff_injective.mp hinj)
      (hopen.comp hV.isOpenMap_subtype_val)⟩
  let c : A ≃ₜ S :=
    { toFun := fun a => ⟨W (a,m),(hcenter _).mpr rfl⟩
      invFun := fun y => (W.symm ⟨y,hOK (hSO y.property)⟩).1
      left_inv := fun a => by
        change (W.symm (W (a,m))).1 = a
        rw [W.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        have hz : (W.symm ⟨y,hOK (hSO y.property)⟩).2 = m := by
          apply Subtype.ext
          apply (hcenter _).mp
          simpa only [W.apply_symm_apply] using y.property
        change (W ((W.symm ⟨y,hOK (hSO y.property)⟩).1,m) : Y) = y
        rw [← hz]
        exact congrArg Subtype.val (W.apply_symm_apply _)
      continuous_toFun := (continuous_subtype_val.comp (W.continuous.comp
        (continuous_id.prodMk continuous_const))).subtype_mk _
      continuous_invFun := continuous_fst.comp (W.symm.continuous.comp
        (continuous_subtype_val.subtype_mk _)) }
  exact ⟨⟨fun p => c (π p),c.continuous.comp π.continuous⟩,hπ,
    c.isLocalHomeomorph.comp hlocalπ⟩

end PoincareConjecture.M76.PrismBelt
