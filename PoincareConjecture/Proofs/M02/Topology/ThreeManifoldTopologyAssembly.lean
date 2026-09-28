import PoincareConjecture.Statements.Ch01.Topology
import PoincareConjecture.Proofs.M02.Orientation
import PoincareConjecture.Proofs.M02.HurewiczAlgebra
import PoincareConjecture.Proofs.M02.HurewiczInjectivity
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.SimplicialCW
import PoincareConjecture.Proofs.M02.CWTransport
import PoincareConjecture.Proofs.M02.Topology.ThreeManifoldTriangulation
import PoincareConjecture.Proofs.M02.Topology.IntegralThreeManifoldTop
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereBase
import PoincareConjecture.Proofs.M02.Topology.HomotopyGroupHomeomorph
import PoincareConjecture.Proofs.M02.Topology.CWThreeSphere

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Set
open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

private theorem piTwo_of_integralHomology_isZero
    (X : TopCat.{u}) [SimplyConnectedSpace X] (x : X)
    (h2 : IsZero (integralHomology X 2)) :
    Subsingleton (HomotopyGroup.Pi 2 X x) := by
  have hlow (k : Nat) (hk : 1 <= k) (hk' : k <= 1) :
      Subsingleton (HomotopyGroup.Pi k X x) := by
    have hk1 : k = 1 := by omega
    subst k
    exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
  refine ⟨fun a b => ?_⟩
  apply homotopyGroupSingularHomologyMap_injective X x 0 hlow
  exact h2.eq_of_tgt _ _

private theorem nonempty_piThree_equiv_int
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (hlow : forall k : Nat, 1 <= k -> k <= 2 ->
      Subsingleton (HomotopyGroup.Pi k X x))
    (e3 : integralHomology X 3 ≃ₗ[Int] Int) :
    Nonempty (HomotopyGroup.Pi 3 X x ≃* Multiplicative Int) := by
  let e := (integralCoefficientHomEquiv (integralHomology X 3)).trans e3.toAddEquiv
  exact exists_homotopyGroupPi_mulEquiv_of_integral_hurewicz_bijective X 2 x e
    ⟨homotopyGroupSingularHomologyMap_injective X x 1 hlow,
      homotopyGroupSingularHomologyMap_surjective X x 2 hlow⟩

private theorem nonempty_threeSphere_piThree_equiv_int
    (s : PoincareConjecture.ThreeSphere) :
    Nonempty (HomotopyGroup.Pi 3 PoincareConjecture.ThreeSphere s ≃* Multiplicative Int) := by
  let X := TopCat.of PoincareConjecture.ThreeSphere
  let : SimplyConnectedSpace X := sphere_simplyConnectedSpace_of_two_lt_finrank
    (E := EuclideanSpace Real (Fin 4)) (by simp)
  apply nonempty_piThree_equiv_int X s
  · intro k hk hk'
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · exact sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 1) (by simp) s
    · exact sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 2) (by simp) s
  · exact integralSphereH3Iso.toLinearEquiv.trans
      (ULift.moduleEquiv : ULift Int ≃ₗ[Int] Int)

private theorem exists_threeDimensionalCW
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] :
    ∃ C : _root_.Topology.CWComplex (univ : Set M),
      letI := C
      (_root_.Topology.RelCWComplex.skeletonLT (univ : Set M)
        ((3 : ℕ∞) + 1) : Set M) = univ := by
  classical
  obtain ⟨I, horder, hfinite, ⟨h⟩, hcard⟩ :=
    exists_compact_three_manifold_finite_triangulation (M := M)
  let := horder
  let := hfinite
  obtain ⟨C, hC⟩ := exists_finite_simplicialCW (finiteOrderComplex I)
    (finiteOrderComplex_finite I)
  let := C
  obtain ⟨hfiniteC, hcellsC⟩ := hC
  let := hfiniteC
  obtain ⟨D, hD⟩ := exists_finiteCW_of_homeomorph h
  let := D
  have hdim (n : Nat) (j : _root_.Topology.CWComplex.cell (univ : Set M) n) :
      n <= 3 := by
    let s := (hcellsC n).some ((hD.2 n).some j)
    have hs := hcard s.val.val s.val.property
    have hsize := s.property
    omega
  refine ⟨D, Set.eq_univ_of_forall fun x => ?_⟩
  have hx : x ∈ ⋃ (n : Nat) (j : _root_.Topology.CWComplex.cell (univ : Set M) n),
      _root_.Topology.RelCWComplex.openCell (C := (univ : Set M)) n j := by
    exact (_root_.Topology.CWComplex.iUnion_openCell_eq_complex
      (C := (univ : Set M))).symm ▸ mem_univ x
  obtain ⟨n, hx⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact _root_.Topology.RelCWComplex.skeletonLT_mono
    (by exact_mod_cast Nat.add_le_add_right (hdim n j) 1)
    (_root_.Topology.RelCWComplex.openCell_subset_skeletonLT
      (C := (univ : Set M)) n j hj)

theorem nonempty_threeManifoldTopologyConclusion_of_integralHomology_two_isZero
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [SimplyConnectedSpace M]
    (h2 : IsZero (integralHomology M 2)) :
    Nonempty (PoincareConjecture.ClosedSimplyConnectedThreeManifoldConclusion (M := M)) := by
  classical
  let x0 : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨C, hdim⟩ := exists_threeDimensionalCW (M := M)
  let := C
  obtain ⟨e3⟩ := nonempty_integralThreeManifoldTop_equiv_int x0
  have hpi1 (x : M) : Subsingleton (HomotopyGroup.Pi 1 M x) :=
    (HomotopyGroup.pi1EquivFundamentalGroup (X := M) (x := x)).injective.subsingleton
  have hpi2 (x : M) : Subsingleton (HomotopyGroup.Pi 2 M x) :=
    piTwo_of_integralHomology_isZero (TopCat.of M) x h2
  have hlow (x : M) (k : Nat) (hk : 1 <= k) (hk' : k <= 2) :
      Subsingleton (HomotopyGroup.Pi k M x) := by
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · exact hpi1 x
    · exact hpi2 x
  let eM (x : M) : HomotopyGroup.Pi 3 M x ≃* Multiplicative Int :=
    Classical.choice (nonempty_piThree_equiv_int (TopCat.of M) x (hlow x) e3)

  let e := Homeomorph.Set.univ M
  let : PathConnectedSpace (univ : Set M) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  have hC1 (x : (univ : Set M)) :
      Subsingleton (HomotopyGroup.Pi 1 (univ : Set M) x) := by
    let := hpi1 x.val
    exact (homotopyGroupHomeomorph 0 e x).injective.subsingleton
  have hC2 (x : (univ : Set M)) :
      Subsingleton (HomotopyGroup.Pi 2 (univ : Set M) x) := by
    let := hpi2 x.val
    exact (homotopyGroupHomeomorph 1 e x).injective.subsingleton
  let eC (x : (univ : Set M)) :
      HomotopyGroup.Pi 3 (univ : Set M) x ≃* Multiplicative Int :=
    (homotopyGroupHomeomorph 2 e x).trans (eM x.val)
  let eS (s : PoincareConjecture.ThreeSphere) :
      HomotopyGroup.Pi 3 PoincareConjecture.ThreeSphere s ≃* Multiplicative Int :=
    Classical.choice (nonempty_threeSphere_piThree_equiv_int s)
  obtain ⟨hCS⟩ := nonempty_homotopyEquiv_sphere_of_cw_three_pi_int hdim hC1 hC2 eC eS
  exact ⟨{
    orientation := nonempty_orientationCompatibleAtlas
    cw_type := C
    basepoint := x0
    fundamental_group_subsingleton := inferInstance
    pi_two_subsingleton := hpi2 x0
    pi_three_integer := ⟨eM x0⟩
    homotopy_three_sphere := ⟨e.symm.toHomotopyEquiv.trans hCS⟩
  }⟩

end PoincareConjecture.Proofs.M02.Topology
