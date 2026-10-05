import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RadialLoops
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Basic

/-!
# Radial homotopy with exact constant-loop representatives

The induced first-jet topology makes radialization homotopic to the identity,
fixing the complete constant-loop records. This justifies the radial-family
construction for MT Definition 18.17, printed p. 430, on based cube classes.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Radialization as a continuous map of the carried loop space.
Source: MT Definition 18.17, p. 430, radial-family derivation. -/
def m59RadialLoopMap : C(C1FreeLoopSpace (M := M), C1FreeLoopSpace (M := M)) :=
  ⟨m59RadialLoop, continuous_m59RadialLoop⟩

/-- The identity-to-radialization homotopy retains the original record at
time zero. Source: MT Definition 18.17, p. 430, radial-family derivation. -/
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

/-- Every time slice fixes the exact constant-loop record. Source:
MT Definition 18.17, p. 430, radial-family derivation. -/
theorem m59RadialLoopHomotopy_constant (t : I) (x : M) :
    m59RadialLoopHomotopy (t, constantC1Loop x) = constantC1Loop x := by
  classical
  change (if t = 0 then constantC1Loop x else m59RadialLoop (constantC1Loop x)) = _
  split_ifs
  · rfl
  · exact m59RadialLoop_constant x

/-- Radialization preserves the based cubical class through a homotopy that
fixes its whole boundary. Source: MT Definition 18.17, p. 430. -/
theorem m59RadialGenLoop_homotopic (n : Nat) (x : M)
    (gamma : GenLoop (Fin n) (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    GenLoop.Homotopic gamma
      (surgeryMappedGenLoop m59RadialLoopMap (m59RadialLoop_constant x) gamma) := by
  refine ⟨{
    toHomotopy := m59RadialLoopHomotopy.compContinuousMap gamma.val
    prop' := fun t z hz => ?_ }⟩
  change m59RadialLoopHomotopy (t, gamma z) = gamma z
  rw [GenLoop.boundary gamma z hz, m59RadialLoopHomotopy_constant]

/-- The actual induced map of radialization is the identity on all based
homotopy groups at constant loops. Source: MT Definition 18.17, p. 430. -/
theorem m59RadialLoopMap_homotopyClass (n : Nat) (x : M)
    (a : HomotopyGroup.Pi n (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    surgeryHomotopyMap m59RadialLoopMap (m59RadialLoop_constant x) a = a := by
  refine Quotient.inductionOn a ?_
  intro gamma
  exact Quotient.sound (m59RadialGenLoop_homotopic n x gamma).symm

end PoincareMT
