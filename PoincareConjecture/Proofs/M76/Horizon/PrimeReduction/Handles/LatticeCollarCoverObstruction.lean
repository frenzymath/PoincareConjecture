import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.RetainedPortCore
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardSphereLift
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CoverSections
import Mathlib.Analysis.Convex.Contractible









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private theorem exists_continuous_finite_closed_cover_map
    {X Y ν : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ν]
    (S : ν → Set X) (f : ∀ i,C(S i,Y)) (hclosed : ∀ i,IsClosed (S i))
    (hcover : ⋃ i,S i = univ)
    (hagree : ∀ i j (x : X) (hi : x ∈ S i) (hj : x ∈ S j),
      f i ⟨x,hi⟩ = f j ⟨x,hj⟩) :
    ∃ F : C(X,Y),∀ i (x : S i),F x = f i x := by
  let F := Set.liftCover S (fun i => f i) hagree hcover
  have hc : Continuous F := by
    apply (locallyFinite_of_finite S).continuous hcover hclosed
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    convert (f i).continuous using 1
    funext x
    exact Set.liftCover_coe (hS := hcover) x
  exact ⟨⟨F,hc⟩,fun i x => Set.liftCover_coe (hf := hagree) (hS := hcover) x⟩

private theorem exists_ball_lift_agreeing_on_sphere
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {p : E → X} (hp : IsCoveringMap p) {Q S C : Set X}
    (hball : IsUnitBallPair V3 Q S) (hS : IsConnected S) (hSC : S ⊆ C)
    (f : C(C,E)) (hf : ∀ x : C,p (f x) = x) :
    ∃ g : C(Q,E),(∀ x : Q,p (g x) = x) ∧
      ∀ x : S,g ⟨x,hball.1 x.property⟩ = f ⟨x,hSC x.property⟩ := by
  classical
  obtain ⟨H,_⟩ := hball.2
  have : ContractibleSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).contractibleSpace ⟨0,mem_closedBall_self zero_le_one⟩
  have : ContractibleSpace Q := H.contractibleSpace_iff.mpr inferInstance
  have : LocallyPathConnectedSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace Q := H.isOpenEmbedding.locallyPathConnectedSpace
  obtain ⟨x,hx⟩ := hS.nonempty
  obtain ⟨g,⟨hg0,hg⟩,_⟩ := hp.existsUnique_continuousMap_lifts
    (⟨Subtype.val,continuous_subtype_val⟩ : C(Q,X)) ⟨x,hball.1 hx⟩
    (f ⟨x,hSC hx⟩) (hf ⟨x,hSC hx⟩)
  have : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  have heq : (fun z : S => g ⟨z,hball.1 z.property⟩) =
      (fun z : S => f ⟨z,hSC z.property⟩) := by
    apply hp.eq_of_comp_eq (by fun_prop) (by fun_prop) (a := ⟨x,hx⟩)
    · exact hg0
    · funext z
      exact (congrFun hg ⟨z,hball.1 z.property⟩).trans (hf ⟨z,hSC z.property⟩).symm
  exact ⟨g,fun z => congrFun hg z,fun z => congrFun heq z⟩

namespace MarkedSphereCut

variable {ι κ α ν : Type*} [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
  {R : Set (LatticeHandleAmbient ι κ L)} (c : MarkedSphereCut e R ν)

omit [Fintype ι] [Fintype κ] in
theorem exists_standard_lattice_collar_lift (i : ν) :
    ∃ f : C(closure (c.collar i),(ι → ℝ) × (κ → ℝ)),
      ∀ x,((f x).1,(QuotientAddGroup.mk (f x).2 :
        (κ → ℝ) ⧸ L.toAddSubgroup)) = (x : LatticeHandleAmbient ι κ L) := by
  let p : ((ι → ℝ) × (κ → ℝ)) → LatticeHandleAmbient ι κ L :=
    fun z => (z.1,QuotientAddGroup.mk z.2)
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod
  obtain ⟨l,_,hl⟩ := (c.portPL (i,false)).exists_standard_lattice_lift ι κ L
  let g : C(c.spheres i,(ι → ℝ) × (κ → ℝ)) :=
    ⟨fun z => l ((c.portPL (i,false)).parametrization.symm (c.portMap (i,false) z)),
      by fun_prop⟩
  let H : C(unitInterval × c.spheres i,LatticeHandleAmbient ι κ L) :=
    ⟨fun z => (c.product i (z.2,z.1) : LatticeHandleAmbient ι κ L),by fun_prop⟩
  have hzero (z : c.spheres i) : H (0,z) = p (g z) := by
    change (c.product i (z,0) : LatticeHandleAmbient ι κ L) = _
    rw [(c.endpoints i z).1]
    change _ = p (l ((c.portPL (i,false)).parametrization.symm (c.portMap (i,false) z)))
    dsimp only [p]
    rw [hl]
    exact (congrArg Subtype.val ((c.portPL (i,false)).parametrization.apply_symm_apply _)).symm
  let F := hp.liftHomotopy H g hzero
  let f : C(closure (c.collar i),(ι → ℝ) × (κ → ℝ)) :=
    ⟨fun x => F ((c.product i).symm x).swap,by fun_prop⟩
  refine ⟨f,fun x => ?_⟩
  have h := congrFun (hp.liftHomotopy_lifts H g hzero) ((c.product i).symm x).swap
  change p (f x) = _
  exact h.trans (congrArg Subtype.val ((c.product i).apply_symm_apply x))

theorem not_collar_two_balls_cover_ambient (i : ν)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (Q : Bool → Set (LatticeHandleAmbient ι κ L))
    (hball : ∀ b,IsUnitBallPair V3 (Q b) (c.ports (i,b)))
    (hdis : Disjoint (Q false) (Q true))
    (hoverlap : ∀ b,closure (c.collar i) ∩ Q b = c.ports (i,b)) :
    closure (c.collar i) ∪ Q false ∪ Q true ≠ univ := by
  classical
  let E := (ι → ℝ) × (κ → ℝ)
  let X := LatticeHandleAmbient ι κ L
  let p : E → X := fun z => (z.1,QuotientAddGroup.mk z.2)
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod
  obtain ⟨f,hf⟩ := c.exists_standard_lattice_collar_lift L i
  have hQ (b : Bool) : IsCompact (Q b) := by
    obtain ⟨_,H,_⟩ := hball b
    exact isCompact_iff_compactSpace.mpr H.symm.compactSpace
  choose g hg hagree using (fun b =>
    exists_ball_lift_agreeing_on_sphere hp (hball b) (c.portPL (i,b)).isConnected
      (c.portClosure (i,b)) f hf)
  let P : Option Bool → Set X := fun j => match j with
    | none => closure (c.collar i)
    | some b => Q b
  let F : ∀ j,C(P j,E) := fun j => match j with
    | none => f
    | some b => g b
  intro hcover
  have hPcover : ⋃ j,P j = univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    have hx : x ∈ closure (c.collar i) ∪ Q false ∪ Q true := hcover.symm ▸ mem_univ x
    rcases hx with (hx | hx) | hx
    · exact ⟨none,hx⟩
    · exact ⟨some false,hx⟩
    · exact ⟨some true,hx⟩
  have hPclosed (j : Option Bool) : IsClosed (P j) := by
    cases j with
    | none => exact isClosed_closure
    | some b => exact (hQ b).isClosed
  have hFagree : ∀ j k (x : X) (hj : x ∈ P j) (hk : x ∈ P k),
      F j ⟨x,hj⟩ = F k ⟨x,hk⟩ := by
    intro j k x hj hk
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some b =>
        exact (hagree b ⟨x,(hoverlap b) ▸ And.intro hj hk⟩).symm
    | some b =>
      cases k with
      | none => exact hagree b ⟨x,(hoverlap b) ▸ And.intro hk hj⟩
      | some d =>
        by_cases hbd : b = d
        · subst d; rfl
        · have hdis' : Disjoint (Q b) (Q d) := by
            cases b <;> cases d
            · exact (hbd rfl).elim
            · exact hdis
            · exact hdis.symm
            · exact (hbd rfl).elim
          exact (disjoint_left.mp hdis' hj hk).elim
  obtain ⟨s,hs⟩ := exists_continuous_finite_closed_cover_map P F hPclosed hPcover hFagree
  have hsection (x : X) : p (s x) = x := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hPcover.symm ▸ mem_univ x)
    rw [hs j ⟨x,hj⟩]
    cases j with
    | none => exact hf ⟨x,hj⟩
    | some b => exact hg b ⟨x,hj⟩
  have hpinj := hp.injective_of_continuous_section s hsection (p 0)
  have hsurj : Function.Surjective s := fun y =>
    ⟨p y,hpinj (hsection (p y))⟩
  have hC : IsCompact (closure (c.collar i)) := by
    have : CompactSpace (c.spheres i) := isCompact_iff_compactSpace.mp (c.spherePL i).isCompact
    exact isCompact_iff_compactSpace.mpr (c.product i).compactSpace
  have hX : IsCompact (univ : Set X) := hcover ▸ (hC.union (hQ false)).union (hQ true)
  have hE : IsCompact (univ : Set E) := by
    simpa only [image_univ,hsurj.range_eq] using hX.image s.continuous
  have hdimE : Module.finrank ℝ E = 3 := by
    simpa only [E,Module.finrank_prod,Module.finrank_pi,Module.finrank_self,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hdim
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdimE]; norm_num)
  exact NormedSpace.unbounded_univ ℝ E hE.isBounded

end MarkedSphereCut
end PoincareConjecture.M76
