import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciNullity
import PoincareLib.Geometry.RicciFlow.Splitting.PartialTrace.Continuity

/-!
# Ricci-nullity propagation from nonnegative sectional curvature

The actual Ricci partial traces are continuous lower-contact heat
supersolutions by the frozen curvature evolution theory. Applying scalar
strong positivity at every finite-dimensional threshold proves spatial
constancy of nullity at positive times and its antitonicity in time.
No rank or earlier-nullity hypothesis is imposed.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- Nonnegative sectional curvature forces spatially constant Ricci nullity
at every positive time of a connected Ricci-flow slab. -/
theorem ricciNullity_eq_on_positive_slice
    (hC : RicciFlowCurvatureCalculus.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    {t : ℝ} (ht : t ∈ Ioc a b) (x y : M) :
    ricciNullity (F.connection t) x = ricciNullity (F.connection t) y := by
  exact ricciNullity_eq_of_heatLowerContacts isOpen_univ isConnected_univ F.connection F.smooth
    (fun r _ => hC.tensor_calculus n M (F.metric r) (F.connection r))
    (fun r hr z _ v => Finset.sum_nonneg fun i _ =>
      hsec r hr z v ((F.metric r).orthonormalBasis z i))
    (fun k hk => ricciPartialTrace_continuousOn_prod hC hab F hk)
    (fun k hk => ricciPartialTrace_heatLowerContacts hC hab F hk
      (fun r hr => hsec r ⟨hr.1.le, hr.2.le⟩)) ht (mem_univ x) (mem_univ y)

/-- Ricci nullity is nonincreasing on the entire closed slab, including its
initial endpoint, under nonnegative sectional curvature. -/
theorem ricciNullity_antitoneOn
    (hC : RicciFlowCurvatureCalculus.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (x : M) : AntitoneOn (fun t => ricciNullity (F.connection t) x) (Icc a b) := by
  exact ricciNullity_antitoneOn_of_heatLowerContacts isOpen_univ isConnected_univ F.connection F.smooth
    (fun r _ => hC.tensor_calculus n M (F.metric r) (F.connection r))
    (fun r hr z _ v => Finset.sum_nonneg fun i _ =>
      hsec r hr z v ((F.metric r).orthonormalBasis z i))
    (fun k hk => ricciPartialTrace_continuousOn_prod hC hab F hk)
    (fun k hk => ricciPartialTrace_heatLowerContacts hC hab F hk
      (fun r hr => hsec r ⟨hr.1.le, hr.2.le⟩)) (mem_univ x)

end PoincareMT.RicciFlow.Splitting
