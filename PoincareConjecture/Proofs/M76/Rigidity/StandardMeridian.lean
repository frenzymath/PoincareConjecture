import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1

variable (L : Submodule ℤ (Fin 1 → ℝ))

def hamiltonStandardMeridianMap (x : V2) :
    LatticeHandleAmbient (Fin 2) (Fin 1) L := (x, 0)

def hamiltonStandardMeridian :
    C(D, LatticeHandle (Fin 2) (Fin 1) L) :=
  ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

def hamiltonStandardMeridianSet : Set (LatticeHandle (Fin 2) (Fin 1) L) :=
  univ ×ˢ {0}

theorem range_hamiltonStandardMeridian :
    range (hamiltonStandardMeridian L) = hamiltonStandardMeridianSet L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨mem_univ _, rfl⟩
  · intro hx
    refine ⟨x.1, ?_⟩
    exact Prod.ext rfl hx.2.symm

theorem isEmbedding_hamiltonStandardMeridian :
    Topology.IsEmbedding (hamiltonStandardMeridian L) :=
  isEmbedding_prodMkLeft 0

def hamiltonStandardMeridianHomeomorph :
    D ≃ₜ hamiltonStandardMeridianSet L where
  toFun x := ⟨(x, 0), mem_univ _, rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext rfl x.property.2.symm)
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

theorem isCompact_hamiltonStandardMeridianSet :
    IsCompact (hamiltonStandardMeridianSet L) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  rw [← range_hamiltonStandardMeridian L, ← image_univ]
  exact isCompact_univ.image (hamiltonStandardMeridian L).continuous

theorem hamiltonStandardMeridian_preimage_boundary :
    hamiltonStandardMeridian L ⁻¹' latticeHandleBoundary (Fin 2) (Fin 1) L =
      {x : D | ‖(x : V2)‖ = 1} := by
  ext x
  change (‖(x : V2)‖ = 1 ∧ True) ↔ ‖(x : V2)‖ = 1
  exact ⟨And.left, fun hx => ⟨hx, trivial⟩⟩

theorem hamiltonStandardMeridian_pi1_injective (x : D) :
    Function.Injective (FundamentalGroup.map (hamiltonStandardMeridian L) x) := by
  let : ContractibleSpace D := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩
  exact Function.injective_of_subsingleton _

theorem StandardLatticeHandleAtlas.polyhedralPL_standardMeridian
    {β : Type*}
    {d : β → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d (hamiltonStandardMeridianMap L) D := by
  obtain ⟨_, C, _, _, _, e, he, _⟩ :=
    (Set.isFinitePLBallPair_unit_cube (ι := Fin 2))
  obtain ⟨f, ⟨K, hK, hKD, _⟩, _⟩ := he
  let a : V2 →ᴬ[ℝ] ((Fin 2 ⊕ Fin 1) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 2) (Fin 1)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((ContinuousLinearMap.id ℝ V2).prod (0 : V2 →L[ℝ] (Fin 1 → ℝ))).toContinuousAffineMap
  have ha : FinitePiecewiseAffineOn a D :=
    ⟨K, hK, hKD, K.affineOnFaces_affine a⟩
  exact hd.polyhedralPL_projection ha

end PoincareConjecture.M76
