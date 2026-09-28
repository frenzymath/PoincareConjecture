import PoincareConjecture.Statements.M50FinitePrefix
import PoincareConjecture.Proofs.M50.ObservedFiniteness
import PoincareConjecture.Proofs.M50.Sec17_2_NoAccumulation




















set_option autoImplicit false

universe u

namespace PoincareConjecture



theorem repairedFinitePrefix : RepairedFinitePrefixTheory.{u} := by
  refine ⟨?_⟩
  intro F C V
  have hlocal := M50.surgery_times_inter_compact_finite F C V
  refine ⟨⟨V, rfl, hlocal, ?_⟩⟩
  intro T
  refine ⟨1, zero_lt_one, ?_⟩
  exact (hlocal (Set.Icc (T - 1) (T + 1)) isCompact_Icc).subset
    (Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self)

end PoincareConjecture
