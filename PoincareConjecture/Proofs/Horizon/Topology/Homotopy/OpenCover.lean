import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.PathDecomposition








noncomputable section
namespace Poincare.Topology

universe u v






theorem loop_nullhomotopic_of_isSimplyConnected
    {X : Type u} [TopologicalSpace X] {A : Set X} {x : X}
    (hx : x ∈ A) (hA : IsSimplyConnected A)
    (γ : Loop x) (hγ : PathIn A γ) :
    γ.Homotopic (Path.refl x) := by
  let xA : A := ⟨x, hx⟩
  let γA : Path xA xA := {
    toFun := fun t => ⟨γ t, hγ ⟨t, rfl⟩⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext γ.source
    target' := Subtype.ext γ.target }
  letI : SimplyConnectedSpace A := hA.simplyConnectedSpace
  have hsub : γA.Homotopic (Path.refl xA) :=
    SimplyConnectedSpace.paths_homotopic γA (Path.refl xA)
  have hamb := hsub.map ⟨Subtype.val, continuous_subtype_val⟩
  have hγA : γA.map continuous_subtype_val = γ := by
    apply Path.ext
    rfl
  have hrefl : (Path.refl xA).map continuous_subtype_val = Path.refl x := by
    apply Path.ext
    rfl
  rw [← hγA, ← hrefl]
  exact hamb



theorem coveredLoopProduct_nullhomotopic
    {X : Type u} [TopologicalSpace X] {x : X} {ι : Type v}
    (carrier : ι → Set X) (hx : ∀ i, x ∈ carrier i)
    (hsc : ∀ i, IsSimplyConnected (carrier i))
    (loops : List (CoveredLoop x))
    (hloops : ∀ p ∈ loops, ∃ i, PathIn (carrier i) p.path) :
    (coveredLoopProduct x loops).Homotopic (Path.refl x) := by
  induction loops with
  | nil => exact Path.Homotopic.refl (Path.refl x)
  | cons p ps ih =>
      obtain ⟨i, hi⟩ := hloops p (by simp)
      have hp : p.path.Homotopic (Path.refl x) :=
        loop_nullhomotopic_of_isSimplyConnected (hx i) (hsc i) p.path hi
      have hps : ∀ q ∈ ps, ∃ i, PathIn (carrier i) q.path := by
        intro q hq
        exact hloops q (by simp [hq])
      exact (Path.Homotopic.hcomp hp (ih hps)).trans
        (Path.Homotopic.refl_trans (Path.refl x))



theorem simplyConnectedSpace_of_pathConnectedOpenCover
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (hsc : ∀ i, IsSimplyConnected (cover.carrier i)) :
    SimplyConnectedSpace X := by
  have hbase (γ : Loop x₀) : γ.Homotopic (Path.refl x₀) := by
    obtain ⟨loops, hγ, hloops⟩ :=
      loop_decomposition_of_pathConnectedOpenCover cover γ
    exact hγ.trans
      (coveredLoopProduct_nullhomotopic cover.carrier cover.base_mem hsc loops hloops)
  have hsub : Subsingleton (FundamentalGroup X x₀) := by
    constructor
    intro a b
    change FundamentalGroup.toPath a = FundamentalGroup.toPath b
    obtain ⟨γ, hγ⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath a)
    obtain ⟨δ, hδ⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath b)
    rw [← hγ, ← hδ]
    exact Path.Homotopic.Quotient.eq.mpr ((hbase γ).trans (hbase δ).symm)
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  let p : Path x x₀ := PathConnectedSpace.somePath x x₀
  let e : FundamentalGroup X x ≃* FundamentalGroup X x₀ :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
  have heq : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = e 1 :=
    hsub.elim _ _
  have hγeq : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1 :=
    e.injective heq
  apply Path.Homotopic.Quotient.eq.mp
  change FundamentalGroup.toPath
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
    FundamentalGroup.toPath 1
  exact congrArg FundamentalGroup.toPath hγeq


end Poincare.Topology
