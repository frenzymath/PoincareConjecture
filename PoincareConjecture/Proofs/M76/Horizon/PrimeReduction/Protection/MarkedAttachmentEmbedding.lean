import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardSphereLift
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.injOn_covering_of_connected_image_subset
    {X E α : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {e : α → OpenPartialHomeomorph X V3} {D B : Set X}
    (b : ChartwisePLBall e D B) {p : E → X} (hp : IsCoveringMap p)
    {C : Set E} (hC : IsPreconnected C) (hCD : MapsTo p C D) :
    InjOn p C := by
  have : ContractibleSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).contractibleSpace
      ⟨0, mem_closedBall_self zero_le_one⟩
  have : ContractibleSpace D := b.parametrization.symm.contractibleSpace
  have : LocallyPathConnectedSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace D :=
    b.parametrization.symm.isOpenEmbedding.locallyPathConnectedSpace
  have : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  intro x hx y hy hxy
  obtain ⟨g, ⟨hg0, hg⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    (⟨Subtype.val, continuous_subtype_val⟩ : C(D, X)) ⟨p x, hCD hx⟩ x rfl
  have heq : (fun z : C => g ⟨p z, hCD z.property⟩) =
      (Subtype.val : C → E) := by
    have hpcont := hp.continuous
    apply hp.eq_of_comp_eq (by fun_prop) continuous_subtype_val (a := ⟨x, hx⟩)
    · funext z
      exact congrFun hg ⟨p z, hCD z.property⟩
    · exact hg0
  calc
    x = g ⟨p x, hCD hx⟩ := (congrFun heq ⟨x, hx⟩).symm
    _ = g ⟨p y, hCD hy⟩ := congrArg g (Subtype.ext hxy)
    _ = y := congrFun heq ⟨y, hy⟩

theorem HamiltonMarkedProtectedBall.quotient_injOn_attaching_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    InjOn (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup)
      (closedBall 0 (3 / 2)) := by
  rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hmark⟩
  · omega
  let : Nonempty ι := Fintype.card_pos_iff.mp hpos
  obtain ⟨a, ha⟩ := (NormedSpace.sphere_nonempty (E := ι → ℝ) (x := 0)).mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  let p : ((ι → ℝ) × (κ → ℝ)) → LatticeHandleAmbient ι κ L :=
    hamiltonMarkedProjection ι κ L
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod
  have hi := b.ball.injOn_covering_of_connected_image_subset hp
    ((convex_singleton a).prod (convex_closedBall (0 : κ → ℝ) (3 / 2))).isPreconnected
    (show MapsTo p ({a} ×ˢ closedBall 0 (3 / 2)) D from by
      rintro z ⟨hz, hzball⟩
      have hzD : p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) := by
        refine ⟨z, ⟨?_, hzball⟩, rfl⟩
        simpa only [mem_singleton_iff.mp hz] using ha
      exact (hmark.symm.subset hzD).1)
  intro x hx y hy hxy
  exact congrArg Prod.snd (hi (x₁ := (a, x)) (x₂ := (a, y))
    ⟨mem_singleton a, hx⟩ ⟨mem_singleton a, hy⟩ (Prod.ext rfl hxy))

theorem HamiltonMarkedProtectedBall.markedProjection_injOn_attaching_patch
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    InjOn (hamiltonMarkedProjection ι κ L)
      (sphere 0 1 ×ˢ closedBall 0 (3 / 2)) := by
  intro x hx y hy hxy
  have hfst : x.1 = y.1 :=
    congrArg (Prod.fst : LatticeHandleAmbient ι κ L → ι → ℝ) hxy
  have hsnd : (QuotientAddGroup.mk x.2 : (κ → ℝ) ⧸ L.toAddSubgroup) =
      QuotientAddGroup.mk y.2 := congrArg Prod.snd hxy
  exact Prod.ext hfst (b.quotient_injOn_attaching_disk hpos hx.2 hy.2 hsnd)

theorem HamiltonMarkedProtectedBall.exists_marked_attaching_homeomorph
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    ∃ H : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ
        hamiltonAttachingBlock ι κ L (3 / 2),
      (∀ x, (H x : LatticeHandleAmbient ι κ L) = hamiltonMarkedProjection ι κ L x) ∧
      ∀ x, (H x : LatticeHandleAmbient ι κ L) ∈
          hamiltonMarkedProjection ι κ L ''
            (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)) ↔
        (x : (ι → ℝ) × (κ → ℝ)).2 ∈ sphere (0 : κ → ℝ) (3 / 2) := by
  let C := sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)
  let f : C → hamiltonAttachingBlock ι κ L (3 / 2) :=
    fun x => ⟨hamiltonMarkedProjection ι κ L x, ⟨x, x.property, rfl⟩⟩
  have : CompactSpace C :=
    isCompact_iff_compactSpace.mp
      ((isCompact_sphere (0 : ι → ℝ) 1).prod (isCompact_closedBall (0 : κ → ℝ) (3 / 2)))
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    exact (continuous_fst.prodMk
      ((continuous_quot_mk).comp continuous_snd)).comp continuous_subtype_val
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact b.markedProjection_injOn_attaching_patch hpos x.property y.property
      (congrArg Subtype.val hxy)
  have hs : Function.Surjective f := by
    rintro ⟨x, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  let H := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorphOfSurjective hs
  refine ⟨H, fun _ => rfl, ?_⟩
  intro x
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy := b.markedProjection_injOn_attaching_patch hpos
      ⟨hy.1, sphere_subset_closedBall hy.2⟩ x.property heq
    exact hxy ▸ hy.2
  · intro hx
    exact ⟨x, ⟨x.property.1, hx⟩, rfl⟩

end PoincareConjecture.M76
