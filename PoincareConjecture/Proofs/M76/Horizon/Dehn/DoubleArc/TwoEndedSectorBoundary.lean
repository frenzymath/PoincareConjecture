import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcEndpointJointBoundary









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem isFinitePLBallPair_two_ended_sector_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F rF : Set E}
    (Q O U : Bool → Set E) (a b : Bool → E)
    (hF : IsFinitePLBallPair P2 F rF)
    (hQ : ∀ j, IsFinitePLBallPair P2 (Q j) (O j ∪ U j))
    (hU : ∀ j, IsFinitePLBallPair ℝ (U j) {a j, b j})
    (hne : ∀ j, a j ≠ b j) (hUrim : ∀ j, U j ⊆ rF)
    (hcontact : ∀ j, F ∩ Q j = U j) (hdisj : Disjoint (Q false) (Q true)) :
    let r₀ := (rF ∪ (O false ∪ U false)) \ (U false \ {a false, b false})
    let rim := (r₀ ∪ (O true ∪ U true)) \ (U true \ {a true, b true})
    IsFinitePLBallPair P2 ((F ∪ Q false) ∪ Q true) rim := by
  let r₀ := (rF ∪ (O false ∪ U false)) \ (U false \ {a false, b false})
  have hfirst : IsFinitePLBallPair P2 (F ∪ Q false) r₀ :=
    hF.union_of_boundary_interval (hQ false) (hU false) (hUrim false)
      (fun _ hz => Or.inr hz) (hne false) (hcontact false)
  have hUQ (j : Bool) : U j ⊆ Q j := (hcontact j).symm.subset.trans inter_subset_right
  have hremains : U true ⊆ r₀ := by
    intro z hz
    refine ⟨Or.inl (hUrim true hz), ?_⟩
    rintro ⟨hu, _⟩
    exact Set.disjoint_left.mp hdisj (hUQ false hu) (hUQ true hz)
  have hsecond : (F ∪ Q false) ∩ Q true = U true := by
    rw [union_inter_distrib_right, hcontact true, hdisj.inter_eq, union_empty]
  exact hfirst.union_of_boundary_interval (hQ true) (hU true) hremains
    (fun _ hz => Or.inr hz) (hne true) hsecond

end PoincareConjecture.M76.Dehn
