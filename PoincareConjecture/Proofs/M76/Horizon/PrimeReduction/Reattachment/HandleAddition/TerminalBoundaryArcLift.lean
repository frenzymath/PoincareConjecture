import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereNormalOrientation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.NullLatticeCircleFilling
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OutermostSurfaceCompression
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_lattice_lift_on_closed_union
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {S A : Set X} (hS : IsClosed S) (hA : IsClosed A)
    [SimplyConnectedSpace S] [LocallyPathConnectedSpace S]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (hinter : IsConnected (S ∩ A))
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup)) :
    ∃ F : C(↥(S ∪ A),κ → ℝ),
      ∀ x, QuotientAddGroup.mk (F x) = q x := by
  classical
  have hp := (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    DiscreteTopology.isDiscrete).isCoveringMap
  obtain ⟨x0,hx0S,hx0A⟩ := hinter.nonempty
  obtain ⟨y0,hy0⟩ := QuotientAddGroup.mk_surjective (q x0)
  let qS : C(S,(κ → ℝ) ⧸ L.toAddSubgroup) := q.comp ⟨Subtype.val,continuous_subtype_val⟩
  let qA : C(A,(κ → ℝ) ⧸ L.toAddSubgroup) := q.comp ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨f,⟨hf0,hf⟩,_⟩ := hp.existsUnique_continuousMap_lifts qS ⟨x0,hx0S⟩ y0 hy0
  obtain ⟨g,⟨hg0,hg⟩,_⟩ := hp.existsUnique_continuousMap_lifts qA ⟨x0,hx0A⟩ y0 hy0
  let : PreconnectedSpace ↥(S ∩ A) := isPreconnected_iff_preconnectedSpace.mp hinter.isPreconnected
  have hagree (x : X) (hxS : x ∈ S) (hxA : x ∈ A) : f ⟨x,hxS⟩ = g ⟨x,hxA⟩ := by
    have hh : (fun z : ↥(S ∩ A) => f ⟨z,z.property.1⟩) =
        fun z : ↥(S ∩ A) => g ⟨z,z.property.2⟩ := by
      apply hp.eq_of_comp_eq (by fun_prop) (by fun_prop) (a := ⟨x0,hx0S,hx0A⟩)
      · exact hf0.trans hg0.symm
      · funext z
        exact (congrFun hf ⟨z,z.property.1⟩).trans (congrFun hg ⟨z,z.property.2⟩).symm
    exact congrFun hh ⟨x,hxS,hxA⟩
  let F : ↥(S ∪ A) → κ → ℝ := fun x =>
    if hx : (x : X) ∈ S then f ⟨x,hx⟩ else g ⟨x,x.property.resolve_left hx⟩
  have hFS (x : ↥(S ∪ A)) (hx : (x : X) ∈ S) : F x = f ⟨x,hx⟩ := by
    simp only [F,dif_pos hx]
  have hFA (x : ↥(S ∪ A)) (hx : (x : X) ∈ A) : F x = g ⟨x,hx⟩ := by
    dsimp only [F]
    split_ifs with hs
    · exact hagree x hs hx
    · rfl
  have hcont : Continuous F := by
    have hs : ContinuousOn F ((Subtype.val : ↥(S ∪ A) → X) ⁻¹' S) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun z : ((Subtype.val : ↥(S ∪ A) → X) ⁻¹' S) =>
          f ⟨z.val,z.property⟩) := by fun_prop
      exact hc.congr (fun z => (hFS z.val z.property).symm)
    have ha : ContinuousOn F ((Subtype.val : ↥(S ∪ A) → X) ⁻¹' A) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun z : ((Subtype.val : ↥(S ∪ A) → X) ⁻¹' A) =>
          g ⟨z.val,z.property⟩) := by fun_prop
      exact hc.congr (fun z => (hFA z.val z.property).symm)
    have hc := hs.union_of_isClosed ha (hS.preimage continuous_subtype_val)
      (hA.preimage continuous_subtype_val)
    have heq : ((Subtype.val : ↥(S ∪ A) → X) ⁻¹' S) ∪
        ((Subtype.val : ↥(S ∪ A) → X) ⁻¹' A) = univ := by
      ext x
      exact iff_true_intro x.property
    rw [heq] at hc
    exact continuousOn_univ.mp hc
  refine ⟨⟨F,hcont⟩,?_⟩
  intro x
  change QuotientAddGroup.mk (F x) = q x
  rcases x.property with hx | hx
  · rw [hFS x hx]
    exact congrFun hf ⟨x,hx⟩
  · rw [hFA x hx]
    exact congrFun hg ⟨x,hx⟩

theorem ChartwisePLSphere.exists_lattice_lift_with_attached_disk
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {A qA W : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W ⊆ A) (hW : IsConnected W)
    (hcontact : f '' A ∩ S = f '' W)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup)) :
    ∃ F : C(↥(S ∪ f '' A),κ → ℝ),
      ∀ x, QuotientAddGroup.mk (F x) = q x := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let fA : A → f '' A := fun x => ⟨f x,mem_image_of_mem f x.property⟩
  have hc : Continuous fA := hf.domRestrict.subtype_mk _
  have hi : Function.Injective fA := fun x y h =>
    Subtype.ext (hfi x.property y.property (congrArg Subtype.val h))
  have hs : Function.Surjective fA := by
    rintro ⟨_,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  let H : A ≃ₜ (f '' A) :=
    (hc.isClosedEmbedding hi).isEmbedding.toHomeomorphOfSurjective hs
  have hcompact := hA.isCompact.image_of_continuousOn hf
  obtain ⟨_,C,_,hcv,hne,G,_,_⟩ := hA
  let : ContractibleSpace C := hcv.contractibleSpace (hne.mono interior_subset)
  let : LocallyPathConnectedSpace C := hcv.locallyPathConnectedSpace
  let : ContractibleSpace A := G.contractibleSpace
  let : LocallyPathConnectedSpace A := G.isOpenEmbedding.locallyPathConnectedSpace
  let : ContractibleSpace (f '' A) := H.symm.contractibleSpace
  let : LocallyPathConnectedSpace (f '' A) := H.symm.isOpenEmbedding.locallyPathConnectedSpace
  let : SimplyConnectedSpace S := s.lifting_connectedness.1
  let : LocallyPathConnectedSpace S := s.lifting_connectedness.2
  have hinter : IsConnected (S ∩ f '' A) := by
    rw [inter_comm,hcontact]
    exact hW.image f (hf.mono hWA)
  exact exists_lattice_lift_on_closed_union L s.isCompact.isClosed
    hcompact.isClosed hinter q

theorem ChartwisePLSphere.exists_terminal_loop_quotient_filling
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {A qA W : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W ⊆ A) (hW : IsConnected W)
    (hcontact : f '' A ∩ S = f '' W)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    (gamma : C(Q2,X)) (hgamma : range gamma ⊆ S ∪ f '' A) :
    ∃ G : C(D2,(κ → ℝ) ⧸ L.toAddSubgroup),
      ∀ x : Q2, G ⟨x,sphere_subset_closedBall x.property⟩ = q (gamma x) := by
  obtain ⟨F,hF⟩ := s.exists_lattice_lift_with_attached_disk L hA hf hfi hWA hW hcontact q
  let gamma' : C(Q2,↥(S ∪ f '' A)) :=
    ⟨fun x => ⟨gamma x,hgamma (mem_range_self x)⟩,gamma.continuous.subtype_mk _⟩
  obtain ⟨G,hG⟩ := ContinuousMap.exists_closedBall_extension_of_contractible (F.comp gamma')
  let p : C(κ → ℝ,(κ → ℝ) ⧸ L.toAddSubgroup) :=
    ⟨QuotientAddGroup.mk,QuotientAddGroup.continuous_mk⟩
  refine ⟨p.comp G,?_⟩
  intro x
  change QuotientAddGroup.mk (G ⟨x,sphere_subset_closedBall x.property⟩) = _
  rw [hG]
  exact hF (gamma' x)

theorem ChartwisePLSphere.exists_terminal_loop_quotient_region
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] (hk : Fintype.card κ = 2)
    {A qA W : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W ⊆ A) (hW : IsConnected W)
    (hcontact : f '' A ∩ S = f '' W)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    (gamma : C(Q2,X)) (hgamma : range gamma ⊆ S ∪ f '' A)
    (hgi : Function.Injective (q.comp gamma)) :
    ∃ G : C(D2,(κ → ℝ) ⧸ L.toAddSubgroup),
      (∀ x : Q2, G ⟨x,sphere_subset_closedBall x.property⟩ = q (gamma x)) ∧
      ∃ U : Set ((κ → ℝ) ⧸ L.toAddSubgroup),
        IsOpen U ∧ IsCompact (closure U) ∧
        frontier U = range (q.comp gamma) ∧ frontier (closure U) = frontier U ∧
        IsSimplyConnected U ∧ closure U ⊆ range G := by
  obtain ⟨G,hG⟩ := s.exists_terminal_loop_quotient_filling L hA hf hfi hWA hW hcontact
    q gamma hgamma
  exact ⟨G,hG,exists_null_lattice_circle_region_in_filling hk L G (q.comp gamma) hgi hG⟩

end PoincareConjecture.M76

