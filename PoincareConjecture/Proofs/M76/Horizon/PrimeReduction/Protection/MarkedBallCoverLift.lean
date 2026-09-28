import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_marked_standard_ball_lift
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    ∃ g : C(D, (ι → ℝ) × (κ → ℝ)),
      Function.Injective g ∧
      (∀ x : D, hamiltonMarkedProjection ι κ L (g x) = x) ∧
      (∀ (x : D) (z : (ι → ℝ) × (κ → ℝ)),
        z ∈ closedBall 0 1 ×ˢ closedBall 0 1 →
        hamiltonMarkedProjection ι κ L z = x → g x = z) ∧
      (∀ (x : D) (z : (ι → ℝ) × (κ → ℝ)),
        z ∈ sphere 0 1 ×ˢ closedBall 0 (3 / 2) →
        hamiltonMarkedProjection ι κ L z = x → g x = z) ∧
      g '' ((Subtype.val : D → LatticeHandleAmbient ι κ L) ⁻¹'
          frontier (latticeHandleDomain ι κ L)) =
        sphere 0 1 ×ˢ closedBall 0 (3 / 2) := by
  rcases b.position with ⟨hzero, _⟩ | ⟨_, hcore, _, _, _, hmark⟩
  · omega
  let p : ((ι → ℝ) × (κ → ℝ)) → LatticeHandleAmbient ι κ L :=
    hamiltonMarkedProjection ι κ L
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod
  have : ContractibleSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).contractibleSpace
      ⟨0, mem_closedBall_self zero_le_one⟩
  have : ContractibleSpace D := b.ball.parametrization.symm.contractibleSpace
  have : LocallyPathConnectedSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace D :=
    b.ball.parametrization.symm.isOpenEmbedding.locallyPathConnectedSpace
  let C := closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1
  have hCD : MapsTo p C D := fun z hz => hcore ⟨z, hz, rfl⟩
  have h0 : (0 : (ι → ℝ) × (κ → ℝ)) ∈ C :=
    ⟨mem_closedBall_self zero_le_one, mem_closedBall_self zero_le_one⟩
  obtain ⟨g, ⟨hg0, hg⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    (⟨Subtype.val, continuous_subtype_val⟩ : C(D, LatticeHandleAmbient ι κ L))
    ⟨p 0, hCD h0⟩ 0 rfl
  have hsection (x : D) : p (g x) = x := congrFun hg x
  have hgi : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact (hsection x).symm.trans ((congrArg p hxy).trans (hsection y))
  have : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp
    ((convex_closedBall (0 : ι → ℝ) 1).prod
      (convex_closedBall (0 : κ → ℝ) 1)).isPreconnected
  have hcoreeq : (fun z : C => g ⟨p z, hCD z.property⟩) =
      (Subtype.val : C → (ι → ℝ) × (κ → ℝ)) := by
    have hpc := hp.continuous
    apply hp.eq_of_comp_eq (by fun_prop) continuous_subtype_val (a := ⟨0, h0⟩)
    · funext z
      exact hsection ⟨p z, hCD z.property⟩
    · exact hg0
  have hcorefix (x : D) (z : (ι → ℝ) × (κ → ℝ))
      (hz : z ∈ C) (heq : p z = x) : g x = z := by
    have hx : (⟨p z, hCD hz⟩ : D) = x := Subtype.ext heq
    exact hx ▸ congrFun hcoreeq ⟨z, hz⟩
  have hpatchD : MapsTo p (sphere 0 1 ×ˢ closedBall 0 (3 / 2)) D := by
    intro z hz
    exact (hmark.symm.subset ⟨z, hz, rfl⟩).1
  have hpatchfix (x : D) (z : (ι → ℝ) × (κ → ℝ))
      (hz : z ∈ sphere 0 1 ×ˢ closedBall 0 (3 / 2)) (heq : p z = x) : g x = z := by
    let K := closedBall (0 : κ → ℝ) (3 / 2)
    have : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp
      (convex_closedBall (0 : κ → ℝ) (3 / 2)).isPreconnected
    have hKD (u : K) : p (z.1, u) ∈ D := hpatchD ⟨hz.1, u.property⟩
    have hK0 : (0 : κ → ℝ) ∈ K := mem_closedBall_self (by norm_num)
    have hfibereq : (fun u : K => g ⟨p (z.1, u), hKD u⟩) =
        (fun u : K => (z.1, (u : κ → ℝ))) := by
      have hpc := hp.continuous
      apply hp.eq_of_comp_eq (by fun_prop) (by fun_prop) (a := ⟨0, hK0⟩)
      · exact hcorefix ⟨p (z.1, 0), hKD ⟨0, hK0⟩⟩ (z.1, 0)
          ⟨sphere_subset_closedBall hz.1, mem_closedBall_self zero_le_one⟩ rfl
      · funext u
        exact hsection ⟨p (z.1, u), hKD u⟩
    have hx : (⟨p (z.1, z.2), hKD ⟨z.2, hz.2⟩⟩ : D) = x := Subtype.ext heq
    exact hx ▸ congrFun hfibereq ⟨z.2, hz.2⟩
  refine ⟨g, hgi, hsection, hcorefix, hpatchfix, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, heq⟩ := hmark.subset ⟨x.property, hx⟩
    exact (hpatchfix x z hz heq).symm ▸ hz
  · intro z hz
    have hx : p z ∈ D ∩ frontier (latticeHandleDomain ι κ L) :=
      hmark.symm.subset ⟨z, hz, rfl⟩
    exact ⟨⟨p z, hx.1⟩, hx.2, hpatchfix ⟨p z, hx.1⟩ z hz rfl⟩

end PoincareConjecture.M76
