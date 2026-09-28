import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedAmbient
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "H0" => LatticeHandle (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "G0" => Multiplicative (Fin 3 → ℤ)

private noncomputable def zeroCoordinate (i : Fin 3) : C(H0, C0) := by
  let c0 : C(H0, C0) := ⟨fun z => (hamiltonZeroHierarchyCoordinates z).1.1,
      continuous_fst.comp (continuous_fst.comp hamiltonZeroHierarchyCoordinates.continuous)⟩
  let c1 : C(H0, C0) := ⟨fun z => (hamiltonZeroHierarchyCoordinates z).1.2,
      continuous_snd.comp (continuous_fst.comp hamiltonZeroHierarchyCoordinates.continuous)⟩
  let c2 : C(H0, C0) := ⟨fun z => (hamiltonZeroHierarchyCoordinates z).2,
      continuous_snd.comp hamiltonZeroHierarchyCoordinates.continuous⟩
  exact ![c0, c1, c2] i

private noncomputable def zeroCoordinateWinding (x : H0) (i : Fin 3) :
    FundamentalGroup H0 x →* Multiplicative ℤ :=
  (HamiltonIntervalTorus.circleFundamentalGroupEquivInt (4 * (16 : ℝ)) (by norm_num)
    ((zeroCoordinate i) x)).toMonoidHom.comp
    (FundamentalGroup.map (zeroCoordinate i) x)

private theorem zeroCoordinateWinding_injective (x : H0) :
    Function.Injective (MonoidHom.pi (zeroCoordinateWinding x)) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
  apply Path.Homotopic.Quotient.eq.mpr
  have hcoord (i : Fin 3) :
      (a.map (zeroCoordinate i).continuous).Homotopic
          (b.map (zeroCoordinate i).continuous) := by
    apply Path.Homotopic.Quotient.exact
    have hi : (zeroCoordinateWinding x i) (Path.Homotopic.Quotient.mk a) =
        (zeroCoordinateWinding x i) (Path.Homotopic.Quotient.mk b) := by
      exact congrArg (fun z : (∀ j : Fin 3, Multiplicative ℤ) => z i) hab
    simpa only [zeroCoordinateWinding, FundamentalGroup.map_apply,
      Path.Homotopic.Quotient.mk_map] using
      (HamiltonIntervalTorus.circleFundamentalGroupEquivInt (4 * (16 : ℝ)) (by norm_num)
        ((zeroCoordinate i) x)).injective hi
  let Q := hamiltonZeroHierarchyCoordinates
  obtain ⟨hzero⟩ := hcoord 0
  obtain ⟨hone⟩ := hcoord 1
  obtain ⟨htwo⟩ := hcoord 2
  refine ⟨{
    toFun := fun z => Q.symm ((hzero z, hone z), htwo z)
    continuous_toFun := Q.symm.continuous.comp
      ((hzero.continuous.prodMk hone.continuous).prodMk htwo.continuous)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    rw [hzero.apply_zero, hone.apply_zero, htwo.apply_zero]
    exact Q.symm_apply_apply (a t)
  · intro t
    rw [hzero.apply_one, hone.apply_one, htwo.apply_one]
    exact Q.symm_apply_apply (b t)
  · intro t s hs
    change Q.symm ((hzero (t, s), hone (t, s)), htwo (t, s)) = a s
    rw [hzero.eq_fst t hs, hone.eq_fst t hs, htwo.eq_fst t hs]
    exact Q.symm_apply_apply (a s)


noncomputable def hamiltonZeroHandleIntegerMap (x : H0) :
    FundamentalGroup H0 x →* G0 :=
  (MulEquiv.funMultiplicative (Fin 3) ℤ).symm.toMonoidHom.comp
    (MonoidHom.pi (zeroCoordinateWinding x))

theorem hamiltonZeroHandleIntegerMap_injective (x : H0) :
    Function.Injective (hamiltonZeroHandleIntegerMap x) := by
  exact (MulEquiv.funMultiplicative (Fin 3) ℤ).symm.injective.comp
    (zeroCoordinateWinding_injective x)


noncomputable def hamiltonZeroAmbientIntegerMap (x : X0) :
    FundamentalGroup X0 x →* G0 :=
  (hamiltonZeroHandleIntegerMap (hamiltonZeroAmbientEquiv x)).comp
    (hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv x).toMonoidHom

theorem hamiltonZeroAmbientIntegerMap_injective (x : X0) :
    Function.Injective (hamiltonZeroAmbientIntegerMap x) :=
  (hamiltonZeroHandleIntegerMap_injective _).comp
    (hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv x).injective

end PoincareConjecture.M76
