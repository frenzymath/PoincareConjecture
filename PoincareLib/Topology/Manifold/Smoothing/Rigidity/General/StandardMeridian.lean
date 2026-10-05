import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonStandardQuotientPL
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

/-!
# The whole standard solid-torus meridian

The actual disk is the zero slice in the original lattice handle.
Its parametrization retains the entire rim, is PL in every supplied
standard target atlas, and induces an injection on fundamental groups.
The latter uses contractibility of the disk, not incompressibility
of the solid-torus boundary. See Hamilton 1976, p. 65, Waldhausen
1968, pp. 59--60, and M76 inputs/Rigidity/derivations/002_standard_meridian.md.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1

variable (L : Submodule ℤ (Fin 1 → ℝ))

/-- The whole affine meridian map into the original quotient ambient.
See Hamilton p. 65 and rigidity derivation 002, whole meridian disk. -/
def hamiltonStandardMeridianMap (x : V2) :
    LatticeHandleAmbient (Fin 2) (Fin 1) L := (x, 0)

/-- The actual zero-slice disk in the marked solid torus.
See Hamilton p. 65 and rigidity derivation 002. -/
def hamiltonStandardMeridian :
    C(D, LatticeHandle (Fin 2) (Fin 1) L) :=
  ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

/-- The entire image of the actual meridian in the original handle.
See rigidity derivation 002. -/
def hamiltonStandardMeridianSet : Set (LatticeHandle (Fin 2) (Fin 1) L) :=
  univ ×ˢ {0}

/-- The literal meridian parametrization has exactly its stated
whole disk image. See rigidity derivation 002. -/
theorem range_hamiltonStandardMeridian :
    range (hamiltonStandardMeridian L) = hamiltonStandardMeridianSet L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨mem_univ _, rfl⟩
  · intro hx
    refine ⟨x.1, ?_⟩
    exact Prod.ext rfl hx.2.symm

/-- Projection to the original disk coordinate makes the meridian
an actual topological embedding. See rigidity derivation 002. -/
theorem isEmbedding_hamiltonStandardMeridian :
    Topology.IsEmbedding (hamiltonStandardMeridian L) :=
  isEmbedding_prodMkLeft 0

/-- The whole meridian carries its original disk parametrization,
with inverse the first-coordinate projection. See derivation 002. -/
def hamiltonStandardMeridianHomeomorph :
    D ≃ₜ hamiltonStandardMeridianSet L where
  toFun x := ⟨(x, 0), mem_univ _, rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext rfl x.property.2.symm)
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

/-- The actual meridian, including its whole rim, is compact.
See Hamilton p. 65 and rigidity derivation 002. -/
theorem isCompact_hamiltonStandardMeridianSet :
    IsCompact (hamiltonStandardMeridianSet L) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  rw [← range_hamiltonStandardMeridian L, ← image_univ]
  exact isCompact_univ.image (hamiltonStandardMeridian L).continuous

/-- Boundary properness holds on the entire disk: its original
norm-one rim is exactly the preimage of the whole handle boundary.
See Hamilton p. 65 and rigidity derivation 002. -/
theorem hamiltonStandardMeridian_preimage_boundary :
    hamiltonStandardMeridian L ⁻¹' latticeHandleBoundary (Fin 2) (Fin 1) L =
      {x : D | ‖(x : V2)‖ = 1} := by
  ext x
  change (‖(x : V2)‖ = 1 ∧ True) ↔ ‖(x : V2)‖ = 1
  exact ⟨And.left, fun hx => ⟨hx, trivial⟩⟩

/-- The actual standard disk is incompressible in Hamilton's sense:
its induced map on fundamental groups is injective at every original
basepoint. This makes no assertion about the boundary torus's group.
See Hamilton p. 65 and rigidity derivation 002. -/
theorem hamiltonStandardMeridian_pi1_injective (x : D) :
    Function.Injective (FundamentalGroup.map (hamiltonStandardMeridian L) x) := by
  let : ContractibleSpace D := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩
  exact Function.injective_of_subsingleton _

/-- The whole original disk map is PL in the supplied standard
target atlas. The finite patches include its complete boundary.
See Hamilton p. 65 and rigidity derivation 002. -/
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

end PoincareMT.M76
