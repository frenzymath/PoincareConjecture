import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition











set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.ProtectedDisks

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1


def transverse (b : Bool) : Set V1 :=
  {y | if b then y 0 ∈ Ioo 1 2 else y 0 ∈ Ioo (-2) (-1)}


noncomputable def height (b : Bool) : V1 := fun _ => if b then (3 / 2 : ℝ) else -(3 / 2 : ℝ)

theorem transverse_isOpen (b : Bool) : IsOpen (transverse b) := by
  cases b <;> exact isOpen_Ioo.preimage (continuous_apply 0)

theorem height_mem_transverse (b : Bool) : height b ∈ transverse b := by
  cases b <;> norm_num [height, transverse]

theorem transverse_norm {b : Bool} {y : V1} (hy : y ∈ transverse b) :
    1 < ‖y‖ ∧ ‖y‖ < 2 := by
  have heq : y = fun _ : Fin 1 => y 0 := funext (fun i => congrArg y (Fin.eq_zero i))
  rw [heq, pi_norm_const, Real.norm_eq_abs]
  cases b
  · change -2 < y 0 ∧ y 0 < -1 at hy
    rw [abs_of_neg (by linarith : y 0 < 0)]
    constructor <;> linarith
  · change 1 < y 0 ∧ y 0 < 2 at hy
    rw [abs_of_pos (by linarith : 0 < y 0)]
    exact hy

theorem transverse_disjoint : Disjoint (transverse false) (transverse true) := by
  apply disjoint_left.mpr
  intro y hy hz
  change -2 < y 0 ∧ y 0 < -1 at hy
  change 1 < y 0 ∧ y 0 < 2 at hz
  linarith


def sourceSlab (b : Bool) : Set (V2 × V1) := D2 ×ˢ transverse b


def slab (h : OpenPartialHomeomorph (V2 × V1) V3) (b : Bool) : Set V3 :=
  h '' sourceSlab b


noncomputable def diskMap (h : OpenPartialHomeomorph (V2 × V1) V3) (b : Bool) (x : V2) : V3 :=
  h (x, height b)

variable (h : OpenPartialHomeomorph (V2 × V1) V3)
  (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source)

include hsource

theorem sourceSlab_subset_source (b : Bool) : sourceSlab b ⊆ h.source :=
  fun _ hx => hsource ⟨hx.1, mem_univ _⟩

theorem slab_subset_target (b : Bool) : slab h b ⊆ h.target := by
  rintro z ⟨x, hx, rfl⟩
  exact h.mapsTo (sourceSlab_subset_source h hsource b hx)

theorem symm_mem_sourceSlab {b : Bool} {z : V3} (hz : z ∈ slab h b) :
    h.symm z ∈ sourceSlab b := by
  obtain ⟨x, hx, rfl⟩ := hz
  rwa [h.left_inv (sourceSlab_subset_source h hsource b hx)]

theorem slab_transverse_norm {b : Bool} {z : V3} (hz : z ∈ slab h b) :
    1 < ‖(h.symm z).2‖ ∧ ‖(h.symm z).2‖ < 2 :=
  transverse_norm (symm_mem_sourceSlab h hsource hz).2

theorem slab_disjoint : Disjoint (slab h false) (slab h true) := by
  apply disjoint_left.mpr
  intro z hm hp
  exact disjoint_left.mp transverse_disjoint
    (symm_mem_sourceSlab h hsource hm).2 (symm_mem_sourceSlab h hsource hp).2


noncomputable def filling (b : Bool) : C(D2, slab h b) where
  toFun x := ⟨diskMap h b x, ⟨(x, height b), ⟨x.property, height_mem_transverse b⟩, rfl⟩⟩
  continuous_toFun := (h.continuousOn.comp_continuous
    (continuous_subtype_val.prodMk continuous_const)
    (fun x => hsource ⟨x.property, mem_univ _⟩)).subtype_mk _

theorem filling_apply (b : Bool) (x : D2) :
    (filling h hsource b x : V3) = h ((x : V2), height b) := rfl

theorem diskMap_injOn (b : Bool) : InjOn (diskMap h b) D2 := by
  intro x hx y hy heq
  exact congrArg Prod.fst (h.injOn (hsource ⟨hx, mem_univ _⟩)
    (hsource ⟨hy, mem_univ _⟩) heq)


noncomputable def rim (b : Bool) : Q2 ≃ₜ (diskMap h b '' Q2) := by
  let f : Q2 → V3 := fun x => diskMap h b x
  have hf : Continuous f := h.continuousOn.comp_continuous
    (continuous_subtype_val.prodMk continuous_const)
    (fun x => hsource ⟨sphere_subset_closedBall x.property, mem_univ _⟩)
  have hfi : Function.Injective f := fun x y hxy => Subtype.ext
    (diskMap_injOn h hsource b (sphere_subset_closedBall x.property)
      (sphere_subset_closedBall y.property) hxy)
  let : CompactSpace Q2 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  have hrange : range f = diskMap h b '' Q2 := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)

theorem rim_apply (b : Bool) (x : Q2) : (rim h hsource b x : V3) = diskMap h b x := rfl

theorem filling_rim (b : Bool) (x : Q2) :
    (filling h hsource b ⟨x, sphere_subset_closedBall x.property⟩ : V3) =
      (rim h hsource b x : V3) := rfl


theorem diskMap_finitePL_rim {N : Set (V2 × V1)}
    (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) (b : Bool) :
    FinitePiecewiseAffineOn (diskMap h b) Q2 := by
  let f : V2 →ᴬ[ℝ] (V2 × V1) :=
    (ContinuousLinearMap.id ℝ V2).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ V2 (height b))
  have hf : FinitePiecewiseAffineOn f Q2 :=
    ⟨squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon,
      squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon,
      (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
        boundary_squareRimPolygon,
      (squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon).affineOnFaces_affine f⟩
  apply hPL.comp_finitePiecewiseAffineOn hf
  intro x hx
  refine ⟨hsource ⟨sphere_subset_closedBall hx, mem_univ _⟩, hboundary ?_⟩
  rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
  exact ⟨hx, mem_univ _⟩

theorem rim_finitePL {N : Set (V2 × V1)}
    (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) (b : Bool) :
    (rim h hsource b).IsFinitePL :=
  ⟨diskMap h b, diskMap_finitePL_rim h hsource hboundary hPL b, fun _ => rfl⟩

end PoincareConjecture.M76.Dehn.ProtectedDisks
