import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.LatticeWinding
import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchySurfaces
import Mathlib.Topology.Instances.AddCircle.Defs

set_option autoImplicit false

namespace PoincareConjecture.M76

theorem torus_fundamentalGroup_nontrivial
    {p : ℝ} (hp : 0 < p) (x : AddCircle p × AddCircle p) :
    Nontrivial (FundamentalGroup (AddCircle p × AddCircle p) x) := by
  let : Nontrivial (FundamentalGroup (AddCircle p) x.1) :=
    (HamiltonIntervalTorus.circleFundamentalGroupEquivInt p hp x.1).symm.injective.nontrivial
  exact (FundamentalGroup.map_prodMk_left_injective x.2 x.1).nontrivial

theorem exists_torus_integer_three_injection
    {p : ℝ} (hp : 0 < p) (x : AddCircle p × AddCircle p) :
    ∃ f : FundamentalGroup (AddCircle p × AddCircle p) x →* Multiplicative (Fin 3 → ℤ),
      Function.Injective f := by
  let c := AddCircle.homeomorphAddCircle p (4 * (16 : ℝ)) (ne_of_gt hp) (by norm_num)
  let h := c.prodCongr c
  let T := hamiltonZeroHierarchyTorus
  let f := (hamiltonZeroHandleIntegerMap (T (h x))).comp
    ((FundamentalGroup.map T (h x)).comp (h.fundamentalGroupMulEquiv x).toMonoidHom)
  exact ⟨f, (hamiltonZeroHandleIntegerMap_injective _).comp
    ((hamiltonZeroHierarchyTorus_pi1_injective _).comp (h.fundamentalGroupMulEquiv x).injective)⟩

theorem torus_model_fundamentalGroup_properties
    {Y : Type*} [TopologicalSpace Y] {p : ℝ} (hp : 0 < p)
    (H : Y ≃ₜ (AddCircle p × AddCircle p)) (x : Y) :
    Nontrivial (FundamentalGroup Y x) ∧
      ∃ f : FundamentalGroup Y x →* Multiplicative (Fin 3 → ℤ), Function.Injective f := by
  let : Nontrivial (FundamentalGroup (AddCircle p × AddCircle p) (H x)) :=
    torus_fundamentalGroup_nontrivial hp (H x)
  obtain ⟨f, hf⟩ := exists_torus_integer_three_injection hp (H x)
  exact ⟨(H.fundamentalGroupMulEquiv x).symm.injective.nontrivial,
    f.comp (H.fundamentalGroupMulEquiv x).toMonoidHom,
    hf.comp (H.fundamentalGroupMulEquiv x).injective⟩

end PoincareConjecture.M76
