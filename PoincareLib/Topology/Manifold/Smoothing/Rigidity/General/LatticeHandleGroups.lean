import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.LatticeBasisQuotient
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLowerPeriodLattice
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.RetractionFundamentalGroup
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.PeriodCircleLoop

/-!
# Nontrivial fundamental groups of arbitrary lattice handles

An actual lattice basis constructs a circle section through every
original basepoint, with a continuous left inverse. The noncontractible
period loop therefore survives in the original handle. This discharges
the nontrivial-group condition in Waldhausen 1968, Theorem 6.1, p. 77,
for the lattice models, without a fixed-period restriction.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "p" => (4 * (128 : ℝ))

/-- Every basepoint of a positive torus-rank lattice handle lies on
an actual retracting period circle. -/
theorem exists_lattice_handle_circle_retraction
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (x : LatticeHandle ι κ L) :
    ∃ (s : C(AddCircle p, LatticeHandle ι κ L))
      (r : C(LatticeHandle ι κ L, AddCircle p)),
      s 0 = x ∧ Function.LeftInverse r s := by
  classical
  obtain ⟨_, _, q, _⟩ := exists_lattice_basis_quotient_homeomorph (Equiv.refl κ)
    L (hamiltonLowerPeriodLattice κ)
  let t := q.trans (hamiltonLowerLatticePiEquiv κ)
  let k : κ := Classical.choice inferInstance
  let v : AddCircle p → κ → AddCircle p :=
    fun z i => if i = k then z + t x.2 k else t x.2 i
  have hv : Continuous v := by
    apply continuous_pi
    intro i
    by_cases hi : i = k
    · simp only [v, hi, if_pos rfl]
      exact continuous_id.add continuous_const
    · simpa only [v, if_neg hi] using
        (continuous_const : Continuous (fun _ : AddCircle p => t x.2 i))
  let s : C(AddCircle p, LatticeHandle ι κ L) :=
    ⟨fun z => (x.1, t.symm (v z)), continuous_const.prodMk (t.symm.continuous.comp hv)⟩
  let r : C(LatticeHandle ι κ L, AddCircle p) :=
    ⟨fun y => t y.2 k - t x.2 k,
      ((continuous_apply k).comp (t.continuous.comp continuous_snd)).sub continuous_const⟩
  refine ⟨s, r, ?_, ?_⟩
  · apply Prod.ext
    · rfl
    change t.symm (v 0) = x.2
    apply t.injective
    rw [t.apply_symm_apply]
    funext i
    by_cases hi : i = k <;> simp [v, hi]
  · intro z
    change t (t.symm (v z)) k - t x.2 k = z
    rw [t.apply_symm_apply]
    simp only [v, if_pos rfl, add_sub_cancel_right]

/-- The based fundamental group is nontrivial at every point of
every actual positive torus-rank lattice handle. -/
theorem nontrivial_pi1_latticeHandle
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (x : LatticeHandle ι κ L) : Nontrivial (FundamentalGroup (LatticeHandle ι κ L) x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : Nontrivial (FundamentalGroup (AddCircle p) 0) :=
    AddCircle.nontrivial_fundamentalGroup_zero p
  obtain ⟨s, r, hx, hsr⟩ := exists_lattice_handle_circle_retraction L x
  have h := (FundamentalGroup.map_injective_of_leftInverse s r hsr 0).nontrivial
  rwa [hx] at h

end PoincareMT.M76
