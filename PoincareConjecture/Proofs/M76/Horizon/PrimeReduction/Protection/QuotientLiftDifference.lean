import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding







set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76

theorem quotient_lift_endpoint_difference
    {κ Y : Type*} [Fintype κ] [TopologicalSpace Y] [PreconnectedSpace Y]
    (L : Submodule ℤ (κ→ℝ)) [DiscreteTopology L]
    (f g : C(Y,κ→ℝ))
    (h : ∀ y, (QuotientAddGroup.mk (f y) : (κ→ℝ) ⧸ L.toAddSubgroup) =
      QuotientAddGroup.mk (g y)) (x y : Y) :
    f y - f x = g y - g x := by
  have hp := (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    DiscreteTopology.isDiscrete).isCoveringMap
  have heq : (fun z => g z + (f x - g x)) = f := by
    apply hp.eq_of_comp_eq (g.continuous.add continuous_const) f.continuous (a := x)
    · funext z
      change (QuotientAddGroup.mk' L.toAddSubgroup) (g z + (f x - g x)) =
        (QuotientAddGroup.mk' L.toAddSubgroup) (f z)
      rw [map_add,map_sub]
      change QuotientAddGroup.mk (g z) +
        ((QuotientAddGroup.mk (f x) : (κ→ℝ) ⧸ L.toAddSubgroup) - QuotientAddGroup.mk (g x)) =
          QuotientAddGroup.mk (f z)
      rw [h x,sub_self,add_zero,h z]
    · dsimp
      abel
  have hy := congrFun heq y
  rw [←hy]
  abel


end PoincareConjecture.M76
