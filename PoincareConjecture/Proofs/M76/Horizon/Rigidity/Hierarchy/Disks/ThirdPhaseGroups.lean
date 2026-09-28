import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SecondPhaseGroups
import Mathlib.Topology.Homotopy.Contractible

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

noncomputable def hamiltonZeroThirdCircleMap (phi : C(H0, H0)) : C(X0, C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).1.1,
    (hamiltonZeroHierarchyCoordinates.continuous.comp
      (phi.continuous.comp hamiltonZeroAmbientEquiv.continuous)).fst.fst⟩

theorem hamiltonZeroThirdPhase_pi1_subsingleton
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {S : Set X0} {c alpha beta d a b : ℝ}
    (halpha : c < alpha) (hbeta : beta < c + p)
    (ha : d < a) (hb : b < d + p)
    (hfirst : S ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : S ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : S ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' {theta})
    (x : S)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    Subsingleton (FundamentalGroup S x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let inc : C(S, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let coords : C(H0, (C0 × C0) × C0) := hamiltonZeroHierarchyCoordinates
  let f := coords.comp (phi.comp (ambient.comp inc))
  have hf : Function.Injective (FundamentalGroup.map f x) := by
    change Function.Injective (FundamentalGroup.map (coords.comp (phi.comp (ambient.comp inc))) x)
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroHierarchyCoordinates.fundamentalGroupMulEquiv
      (phi (ambient (inc x)))).injective.comp
      ((F.fundamentalGroup_map_bijective (ambient (inc x))).1.comp
        ((hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv (inc x)).injective.comp hinj))
  let J := AddCircle.openPartialHomeomorphCoe p c
  let K := AddCircle.openPartialHomeomorphCoe p d
  have hJ (y : S) : (f y).2 ∈ J.target := by
    obtain ⟨u, hu, he⟩ := hfirst y.property
    have hs : u ∈ J.source := ⟨halpha.trans_le hu.1, hu.2.trans_lt hbeta⟩
    change hamiltonZeroCircleMap phi y ∈ J.target
    rw [← he]
    exact J.map_source hs
  have hK (y : S) : (f y).1.2 ∈ K.target := by
    obtain ⟨u, hu, he⟩ := hsecond y.property
    have hs : u ∈ K.source := ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
    change hamiltonZeroSecondCircleMap phi y ∈ K.target
    rw [← he]
    exact K.map_source hs
  let lift : C(S, ℝ × ℝ) :=
    ⟨fun y => (J.symm (f y).2, K.symm (f y).1.2),
      (J.continuousOn_symm.comp_continuous f.continuous.snd hJ).prodMk
        (K.continuousOn_symm.comp_continuous f.continuous.fst.snd hK)⟩
  let sectionMap : C(ℝ × ℝ, (C0 × C0) × C0) :=
    ⟨fun z => ((theta, (z.2 : C0)), (z.1 : C0)),
      (continuous_const.prodMk ((AddCircle.continuous_mk' p).comp continuous_snd)).prodMk
        ((AddCircle.continuous_mk' p).comp continuous_fst)⟩
  have hfactor : sectionMap.comp lift = f := by
    apply ContinuousMap.ext
    intro y
    apply Prod.ext
    · apply Prod.ext
      · exact (hthird y.property).symm
      · exact K.right_inv (hK y)
    · exact J.right_inv (hJ y)
  rw [← hfactor, FundamentalGroup.map_comp] at hf
  have hg : Function.Injective (FundamentalGroup.map lift x) :=
    Function.Injective.of_comp hf
  exact hg.subsingleton

theorem isSimplyConnected_hamiltonZeroThirdPhase
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {S : Set X0} {c alpha beta d a b : ℝ}
    (halpha : c < alpha) (hbeta : beta < c + p)
    (ha : d < a) (hb : b < d + p)
    (hfirst : S ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : S ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : S ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' {theta})
    (hconn : IsPathConnected S)
    (hinj : ∀ x : S, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    IsSimplyConnected S := by
  let : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp hconn
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x q => ?_⟩
  have hs := hamiltonZeroThirdPhase_pi1_subsingleton phi F
    halpha hbeta ha hb hfirst hsecond theta hthird x (hinj x)
  exact Path.Homotopic.Quotient.eq.mp
    (hs.elim (Path.Homotopic.Quotient.mk q) (Path.Homotopic.Quotient.mk (Path.refl x)))

end PoincareConjecture.M76
