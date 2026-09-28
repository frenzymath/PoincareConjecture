import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.LoopTransfer
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourcePhaseSets



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem sourcePhase_slab_pi1_injective_of_motion
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    (phi : C(H, H)) {u v : ℝ} {theta : C}
    (he : PLDomain e (sourceSlab phi u v))
    (hSF : sourceSurface phi theta ⊆ frontier (sourceSlab phi u v))
    (hpi : ∀ x : sourceSurface phi theta,
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSF) x))
    (D : C(unitInterval × sourceSurface phi theta, sourceSurface phi theta))
    (hzero : ∀ x, D (0, x) = x)
    (hkeep : ∀ t, MapsTo (fun x => D (t, x))
      {x : sourceSurface phi theta | (x : X) ∉ frontier R}
      {x : sourceSurface phi theta | (x : X) ∉ frontier R})
    (hend : ∀ x, (D (1, x) : X) ∉ frontier R)
    (hMF : sourceSurface phi theta \ frontier R ⊆ frontier (sourceSlab phi u v))
    (hker : ∀ x : ↥(sourceSurface phi theta \ frontier R),
      ∀ c : FundamentalGroup ↥(sourceSurface phi theta \ frontier R) x,
        FundamentalGroup.map
          (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) x c = 1 →
        FundamentalGroup.map (ContinuousMap.inclusion hMF) x c = 1) :
    ∃ hSN : sourceSurface phi theta ⊆ sourceSlab phi u v,
      ∀ x : sourceSurface phi theta,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x) := by
  let A : Set (sourceSurface phi theta) := {x | (x : X) ∉ frontier R}
  let M := sourceSurface phi theta \ frontier R
  let E : A ≃ₜ M := {
    toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let hSN := hSF.trans he.closed.frontier_subset
  let f := ContinuousMap.inclusion hSN
  let g := ContinuousMap.inclusion hSF
  refine ⟨hSN, fun x => pi1_injective_of_inward_motion_and_kernel f g D hzero hkeep hend hpi ?_ x⟩
  intro y c hc
  let k : C(A, M) := ⟨E, E.continuous⟩
  have hk : FundamentalGroup.map
      (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) (E y)
        (FundamentalGroup.map k y c) = 1 := by
    exact (FundamentalGroup.map_comp_apply k
      (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) y c).symm.trans hc
  have h := hker (E y) (FundamentalGroup.map k y c) hk
  exact (FundamentalGroup.map_comp_apply k (ContinuousMap.inclusion hMF) y c).trans h

end PoincareConjecture.M76.HamiltonIntervalTorus
