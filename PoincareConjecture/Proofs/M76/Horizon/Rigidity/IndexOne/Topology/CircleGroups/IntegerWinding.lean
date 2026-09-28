import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.SpecificGroups.Cyclic











set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus



noncomputable def integerPeriodDeckEquiv (p : ℝ) (hp : 0 < p) :
    ℤ ≃+ AddSubgroup.zmultiples p := by
  let f : ℤ →+ AddSubgroup.zmultiples p :=
    { toFun := fun n => ⟨n • p, AddSubgroup.zsmul_mem_zmultiples p n⟩
      map_zero' := Subtype.ext (zero_zsmul p)
      map_add' := fun n m => Subtype.ext (add_zsmul p n m) }
  apply AddEquiv.ofBijective f
  constructor
  · intro n m h
    have hs : n • p = m • p := congrArg Subtype.val h
    have hr : (n : ℝ) * p = (m : ℝ) * p := by
      simpa only [zsmul_eq_mul] using hs
    exact Int.cast_injective (mul_right_cancel₀ hp.ne' hr)
  · intro z
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp z.property
    exact ⟨n, Subtype.ext hn⟩



noncomputable def circleFundamentalGroupEquivInt (p : ℝ) (hp : 0 < p)
    (x : AddCircle p) : FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ := by
  classical
  let cov := AddCircle.isAddQuotientCoveringMap_coe p
  let e : ((↑) : ℝ → AddCircle p) ⁻¹' {x} :=
    ⟨(cov.surjective x).choose, (cov.surjective x).choose_spec⟩
  exact (cov.fundamentalGroupEquiv e).trans
    ((MulOpposite.opMulEquiv : Multiplicative (AddSubgroup.zmultiples p) ≃* _).symm.trans
      (AddEquiv.toMultiplicative (integerPeriodDeckEquiv p hp).symm))


theorem circleFundamentalGroup_isCyclic (p : ℝ) (hp : 0 < p) (x : AddCircle p) :
    IsCyclic (FundamentalGroup (AddCircle p) x) :=
  (circleFundamentalGroupEquivInt p hp x).isCyclic.mpr inferInstance

end PoincareConjecture.M76.HamiltonIntervalTorus
