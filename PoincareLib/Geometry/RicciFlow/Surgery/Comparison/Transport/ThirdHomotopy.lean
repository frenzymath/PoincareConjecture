import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Topology.HomotopyFunctoriality
/-!
# Based third-homotopy transport of the comparison map

The induced map is exactly `surgeryHomotopyMap`, including its supplied
basepoint equality. Homotopy equivalences induce bijections, and free
homotopies into a simply connected target induce equal based maps.
Sources: Morgan--Tian, pp. 430--431 and Claim 18.22, p. 433; Hatcher,
Section 4.1, pp. 341--342; the 2026-09-18 SurgeryComparison.Transport full contract.
-/

set_option autoImplicit false

open scoped Topology unitInterval

universe u v

namespace PoincareMT.SurgeryComparison.Topology

noncomputable section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The frozen surgery quotient map is the published cubical
postcomposition map; Morgan--Tian, pp. 430--431. -/
theorem surgeryHomotopyMap_eq_postcomp (n : ℕ) (f : C(X, Y)) (x : X) :
    surgeryHomotopyMap (n := n + 1) f (show f x = f x from rfl) =
      Poincare.Topology.homotopyGroupPostcomp n f x := rfl

/-- Freely homotopic maps with the same prescribed basepoint induce the
same actual based homotopy map into a simply connected target. This is
the basepoint-trace argument in the SurgeryComparison.Transport full contract, following Hatcher,
Section 4.1, p. 342. -/
theorem surgeryHomotopyMap_eq_of_homotopic [SimplyConnectedSpace Y]
    {x : X} {y : Y} {n : ℕ} (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (hfg : f.Homotopic g) (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap f hf a = surgeryHomotopyMap g hg a := by
  obtain ⟨H⟩ := hfg
  induction a using Quotient.inductionOn with | h a =>
    let p : Path y y :=
      { toFun := fun t => H (t, x)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := (H.apply_zero x).trans hf
        target' := (H.apply_one x).trans hg }
    apply Quotient.sound
    apply Topology.homotopicRel_of_uniform_boundary_trace
      (surgeryMappedGenLoop f hf a) (surgeryMappedGenLoop g hg a)
      (H.compContinuousMap a.val) p
    intro t z
    exact congrArg (fun w => H (t, w)) (a.property z.val z.property)

/-- Bijectivity is attached to the exact forward continuous map of the
homotopy equivalence, with the contract's chosen target point. Hatcher,
p. 342; Morgan--Tian, pp. 430--431. -/
theorem surgeryHomotopyMap_bijective_of_homotopyEquiv
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : C(X, Y)) (hf : f x = y)
    (he : ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f) :
    Function.Bijective (surgeryHomotopyMap (n := n + 1) f hf) := by
  obtain ⟨e, rfl⟩ := he
  subst y
  rw [surgeryHomotopyMap_eq_postcomp]
  exact Topology.homotopyGroupPostcomp_bijective_of_homotopyEquiv n e x

/-- The pi3 specialization used for the selected surgery comparison map;
Morgan--Tian, pp. 430--431 and Claim 18.22. -/
theorem surgeryPiThree_bijective_of_homotopyEquiv
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    (he : ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f) :
    Function.Bijective (surgeryHomotopyMap (n := 3) f hf) :=
  surgeryHomotopyMap_bijective_of_homotopyEquiv 2 f hf he

end

end PoincareMT.SurgeryComparison.Topology
