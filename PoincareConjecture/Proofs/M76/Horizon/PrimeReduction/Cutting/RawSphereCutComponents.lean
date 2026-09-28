import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawSphereCutRetraction

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_raw_sphere_cut_component_map
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    (R Q : Set X) (O S : κ → Set X)
    (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i, O i) (hcQ : IsClosed Q)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1 / 2)
    (hSC : ∀ i, S i ⊆ closure (O i)) :
    ∃ r : X → X,
      ContinuousOn r (R \ ⋃ i, S i) ∧
      MapsTo r (R \ ⋃ i, S i) Q ∧ EqOn r id Q ∧
      (∀ x ∈ R \ ⋃ i, S i, r x ∈ connectedComponentIn (R \ ⋃ i, S i) x) ∧
      (∀ x ∈ Q, connectedComponentIn Q x = connectedComponentIn (R \ ⋃ i, S i) x ∩ Q) ∧
      ∀ x ∈ R \ ⋃ i, S i,
        connectedComponentIn Q (r x) = connectedComponentIn (R \ ⋃ i, S i) x ∩ Q := by
  classical
  let U := R \ ⋃ i, S i
  have hQU : Q ⊆ U := by
    intro x hx
    have hx' := hQ.subset hx
    refine ⟨hx'.1,?_⟩
    intro hs
    obtain ⟨i,hi⟩ := mem_iUnion.mp hs
    let z := (W i).symm ⟨x,hSC i hi⟩
    have hWz : (W i z : X) = x := congrArg Subtype.val ((W i).apply_symm_apply _)
    have ht : (z.2 : ℝ) = 1 / 2 := (hS i z).mp (hWz.symm ▸ hi)
    have hxO : x ∈ O i := hWz ▸ (hO i z).mpr (by rw [ht]; norm_num)
    exact hx'.2 (mem_iUnion.mpr ⟨i,hxO⟩)
  obtain ⟨F,hF0,hF1,hFfix⟩ :=
    exists_raw_sphere_cut_retraction R Q O S W hQ hcQ hCR hdis hO hS hSC
  let r : X → X := fun x => if hx : x ∈ U then (F (1,⟨x,hx⟩) : X) else x
  have hr (x : U) : r x = (F (1,x) : X) := by
    simp only [r,dif_pos x.property]
    rfl
  have hrc : ContinuousOn r U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : U.domRestrict r = fun x : U => (F (1,x) : X) := funext hr
    rw [heq]
    exact continuous_subtype_val.comp (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hrQ : MapsTo r U Q := by
    intro x hx
    rw [hr ⟨x,hx⟩]
    exact hF1 ⟨x,hx⟩
  have hrfix : EqOn r id Q := by
    intro x hx
    rw [hr ⟨x,hQU hx⟩,hFfix 1 _ hx]
    rfl
  have hrcc (x : X) (hx : x ∈ U) : r x ∈ connectedComponentIn U x := by
    let p : unitInterval → X := fun t => (F (t,⟨x,hx⟩) : X)
    have hp : Continuous p := continuous_subtype_val.comp
      (F.continuous.comp (continuous_id.prodMk continuous_const))
    have hp0 : p 0 = x := congrArg Subtype.val (hF0 ⟨x,hx⟩)
    have hp1 : p 1 = r x := (hr ⟨x,hx⟩).symm
    have hpU : range p ⊆ U := by
      rintro _ ⟨t,rfl⟩
      exact (F (t,⟨x,hx⟩)).property
    have hsub := (isConnected_range hp).isPreconnected.subset_connectedComponentIn
      (show x ∈ range p from ⟨0,hp0⟩) hpU
    exact hsub ⟨1,hp1⟩
  have hcomponent (x : X) (hx : x ∈ Q) :
      connectedComponentIn Q x = connectedComponentIn U x ∩ Q := by
    apply Subset.antisymm
    · exact subset_inter (connectedComponentIn_mono x hQU) (connectedComponentIn_subset _ _)
    · rintro y ⟨hy,hyQ⟩
      have him := hrc.mapsTo_connectedComponentIn (hQU hx) hy
      have hsubset : r '' U ⊆ Q := mapsTo_iff_image_subset.mp hrQ
      have hh := connectedComponentIn_mono (r x) hsubset him
      rwa [hrfix hx,hrfix hyQ] at hh
  refine ⟨r,hrc,hrQ,hrfix,hrcc,hcomponent,?_⟩
  intro x hx
  rw [hcomponent _ (hrQ hx),connectedComponentIn_eq (hrcc x hx)]

end PoincareConjecture.M76
