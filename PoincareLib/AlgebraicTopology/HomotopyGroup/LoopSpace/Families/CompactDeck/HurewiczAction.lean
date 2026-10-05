import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.HurewiczTransport
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Basepoint.GenLoopWhisker
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Theory

/-!
# Homology-trivial self-maps and the actual pi3 action

The Hurewicz map commutes with the frozen surgery postcomposition map and
the constructed cubical basepoint transport. Injectivity converts identity
on integral H3 into equality with transport on pi3. The compact manifold
specialization applies the supplied M02 topology provider and uses its
vanishing pi2 conclusion at the required image basepoint.

Sources: MT Claim 18.16, printed p. 430; Hatcher, Theorem 4.32, pp. 366-367,
and the M59 compact-cover-deck derivation.
-/

set_option autoImplicit false

open CategoryTheory
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareMT.Proofs.M59

open M02

/-- Hurewicz classes of the actual quotient transport agree with the original
classes. Source: Hatcher, Section 4.1, pp. 341-342. -/
theorem homotopyGroupSingularHomologyMap_transport
    {X : Type u} [TopologicalSpace X] {n : ℕ} {x y : X}
    (p : Path x y) (a : HomotopyGroup.Pi (n + 1) X x) :
    homotopyGroupSingularHomologyMap (ModuleCat.of ℤ (ULift.{u} ℤ))
      (TopCat.of X) n y ((m59HigherBasepointTransport X (n + 1)).map p a) =
    homotopyGroupSingularHomologyMap (ModuleCat.of ℤ (ULift.{u} ℤ))
      (TopCat.of X) n x a := by
  refine Quotient.inductionOn a ?_
  intro a
  exact genLoopSingularHomologyClass_boundaryTransport _ (TopCat.of X) p a

/-- Identity on actual integral H3 identifies postcomposition on pi3 with
transport to the image point. Source: Hatcher, Theorem 4.32, pp. 366-367. -/
theorem piThreeMap_eq_transport_of_homologyMap_eq_id
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
    (f : C(X, X)) (x : X) (p : Path x (f x))
    (hpiTwo : Subsingleton (HomotopyGroup.Pi 2 X (f x)))
    (hH : surgeryThirdHomologyMap f = LinearMap.id)
    (a : HomotopyGroup.Pi 3 X x) :
    surgeryHomotopyMap (n := 3) f rfl a =
      (m59HigherBasepointTransport X 3).map p a := by
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  have hlow (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 2) :
      Subsingleton (HomotopyGroup.Pi k X (f x)) := by
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
    · exact hpiTwo
  have hH' : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R 3 = 𝟙 _ := by
    apply ModuleCat.hom_ext
    exact hH
  apply homotopyGroupSingularHomologyMap_injective (TopCat.of X) (f x) 1 hlow
  rw [homotopyGroupSingularHomologyMap_transport]
  change homotopyGroupSingularHomologyMap R (TopCat.of X) 2 (f x)
    (homotopyGroupMap (Fin 3) f rfl a) = _
  have hnat := (homotopyGroupSingularHomologyMap_naturality R
    (TopCat.ofHom f) 2 x a).symm
  change homotopyGroupSingularHomologyMap R (TopCat.of X) 2 (f x)
    (homotopyGroupMap (Fin 3) f rfl a) =
      homotopyGroupSingularHomologyMap R (TopCat.of X) 2 x a ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R 3 at hnat
  simpa only [hH', Category.comp_id] using hnat

/-- Applied M02 supplies the low connectivity needed to transfer an integral
homology deck calculation to pi3. Source: MT Claim 18.16, printed p. 430. -/
theorem compactThree_piThreeMap_eq_transport_of_homologyMap_eq_id
    (P02 : RepairedClosedTopologyProvider.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (f : C(M, M)) (x : M) (p : Path x (f x))
    (hH : surgeryThirdHomologyMap f = LinearMap.id)
    (a : HomotopyGroup.Pi 3 M x) :
    surgeryHomotopyMap (n := 3) f rfl a =
      (m59HigherBasepointTransport M 3).map p a := by
  obtain ⟨T⟩ := P02 (M := M)
  let B := m59HigherBasepointTransport M 2
  let q : Path (f x) T.basepoint := PathConnectedSpace.somePath (f x) T.basepoint
  have hi : Function.Injective (B.map q) :=
    (show Function.LeftInverse (B.map q.symm) (B.map q) from B.map_left_inverse q).injective
  let := T.pi_two_subsingleton
  exact piThreeMap_eq_transport_of_homologyMap_eq_id f x p
    hi.subsingleton hH a

end PoincareMT.Proofs.M59
