import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.OneSheet.IdentityHomotopy

/-!
# Cylinder lifts between covered boundary circles

Lift the actual cylinder map from its lower boundary covering. If the upper
boundary is also a covering, its lift is a homeomorphism homotopic to the
identity. The two boundary coverings may have different source and target
circle periods.
-/

noncomputable section

open scoped unitInterval

namespace IsCoveringMap

/-- A cylinder whose two boundary maps are coverings lifts from the identity
on its lower boundary to a homeomorphism on its upper boundary. -/
theorem exists_cylinder_lift_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace X] [PathConnectedSpace X]
    {g : C(X, Y)} (hg : IsCoveringMap g)
    (f : C(I × X, Y)) (hzero : ∀ x, f (0, x) = g x)
    (hone : IsCoveringMap (fun x => f (1, x))) :
    ∃ H : X ≃ₜ X, ∃ L : (ContinuousMap.id X).Homotopy (H : C(X, X)),
      ∀ t x, g (L (t, x)) = f (t, x) := by
  let lift : C(I × X, X) := hg.liftHomotopy f (ContinuousMap.id X) hzero
  have hlift : ∀ t x, g (lift (t, x)) = f (t, x) :=
    fun t x => congr_fun (hg.liftHomotopy_lifts f (ContinuousMap.id X) hzero) (t, x)
  let last : C(X, X) :=
    ⟨fun x => lift (1, x), lift.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let L : (ContinuousMap.id X).Homotopy last :=
    { lift with
      map_zero_left := hg.liftHomotopy_zero f (ContinuousMap.id X) hzero
      map_one_left := fun _ => rfl }
  have hcomp : IsLocalHomeomorph (g ∘ last) := by
    convert hone.isLocalHomeomorph using 1
    exact funext (hlift 1)
  have hlast : IsCoveringMap last :=
    isLocalHomeomorph_iff_isCoveringMap.mp
      (hcomp.of_comp hg.isLocalHomeomorph last.continuous)
  exact ⟨hlast.homeomorphOfHomotopyId L, L, hlift⟩

/-- The cylinder lifting construction for arbitrary positive source and
target circle periods. Its upper boundary identification is homotopic to the
identity, so its orientation agrees with the lower boundary identification. -/
theorem exists_addCircle_cylinder_lift_homeomorph
    {p q : ℝ} (hp : 0 < p) (_hq : 0 < q)
    {g : C(AddCircle p, AddCircle q)} (hg : IsCoveringMap g)
    (f : C(I × AddCircle p, AddCircle q))
    (hzero : ∀ x, f (0, x) = g x)
    (hone : IsCoveringMap (fun x => f (1, x))) :
    ∃ H : AddCircle p ≃ₜ AddCircle p,
      ∃ L : (ContinuousMap.id (AddCircle p)).Homotopy
        (H : C(AddCircle p, AddCircle p)),
        ∀ t x, g (L (t, x)) = f (t, x) := by
  let : Fact (0 < p) := ⟨hp⟩
  exact hg.exists_cylinder_lift_homeomorph f hzero hone

end IsCoveringMap
