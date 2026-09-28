import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RadialLoops
import PoincareConjecture.Definitions.Ch15.SurgeryComparison

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def m59RadialLoopMap : C(C1FreeLoopSpace (M := M), C1FreeLoopSpace (M := M)) :=
  ⟨m59RadialLoop, continuous_m59RadialLoop⟩

def m59RadialLoopHomotopy :
    (ContinuousMap.id (C1FreeLoopSpace (M := M))).Homotopy m59RadialLoopMap := by
  classical
  exact {
    toFun := fun p => if p.1 = 0 then p.2 else m59RadialLoop p.2
    continuous_toFun := continuous_of_loop_firstJet_eq continuous_snd
      (fun p z => by split_ifs <;> first | rfl | exact m59RadialLoop_apply p.2 z)
      (fun p z => by split_ifs <;> first | rfl | exact m59RadialLoop_tangent p.2 z)
    map_zero_left := fun _ => if_pos rfl
    map_one_left := fun _ => if_neg one_ne_zero }

theorem m59RadialLoopHomotopy_constant (t : I) (x : M) :
    m59RadialLoopHomotopy (t, constantC1Loop x) = constantC1Loop x := by
  classical
  change (if t = 0 then constantC1Loop x else m59RadialLoop (constantC1Loop x)) = _
  split_ifs
  · rfl
  · exact m59RadialLoop_constant x

theorem m59RadialGenLoop_homotopic (n : Nat) (x : M)
    (gamma : GenLoop (Fin n) (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    GenLoop.Homotopic gamma
      (surgeryMappedGenLoop m59RadialLoopMap (m59RadialLoop_constant x) gamma) := by
  refine ⟨{
    toHomotopy := m59RadialLoopHomotopy.compContinuousMap gamma.val
    prop' := fun t z hz => ?_ }⟩
  change m59RadialLoopHomotopy (t, gamma z) = gamma z
  rw [GenLoop.boundary gamma z hz, m59RadialLoopHomotopy_constant]

theorem m59RadialLoopMap_homotopyClass (n : Nat) (x : M)
    (a : HomotopyGroup.Pi n (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    surgeryHomotopyMap m59RadialLoopMap (m59RadialLoop_constant x) a = a := by
  refine Quotient.inductionOn a ?_
  intro gamma
  exact Quotient.sound (m59RadialGenLoop_homotopic n x gamma).symm

end PoincareConjecture
