import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Mathlib.RadialSimplex
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition











set_option autoImplicit false

open Set Metric Geometry Topology NormedSpace
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1


def source : Set (V1 × V2) := closedBall (0 : V1) 1 ×ˢ Q2


def sourceShell : Set (V1 × V2) :=
  closedBall (0 : V1) 1 ×ˢ {y : V2 | 1 < ‖y‖ ∧ ‖y‖ < 2}


def shell (h : OpenPartialHomeomorph (V1 × V2) V3) : Set V3 := h '' sourceShell


def endpoint (b : Bool) : V1 := fun _ ↦ if b then 1 else -1

theorem endpoint_mem_sphere (b : Bool) : endpoint b ∈ sphere (0 : V1) 1 := by
  rw [mem_sphere_zero_iff_norm]
  change ‖fun _ : Fin 1 ↦ if b then (1 : ℝ) else -1‖ = 1
  cases b <;> simp


noncomputable def coordinates : (V1 × V2) →L[ℝ] (V1 × V2) :=
  (ContinuousLinearMap.fst ℝ V1 V2).prod
    ((3 / 2 : ℝ) • ContinuousLinearMap.snd ℝ V1 V2)

theorem coordinates_apply (x : V1 × V2) :
    coordinates x = (x.1, (3 / 2 : ℝ) • x.2) := rfl

theorem coordinates_mem_sourceShell {x : V1 × V2} (hx : x ∈ source) :
    coordinates x ∈ sourceShell := by
  refine ⟨hx.1, ?_⟩
  have hn : ‖x.2‖ = 1 := mem_sphere_zero_iff_norm.mp hx.2
  change 1 < ‖(3 / 2 : ℝ) • x.2‖ ∧ ‖(3 / 2 : ℝ) • x.2‖ < 2
  norm_num [norm_smul, hn]

variable (h : OpenPartialHomeomorph (V1 × V2) V3)
  (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)

include hsource

theorem sourceShell_subset_source : sourceShell ⊆ h.source :=
  fun _ hx ↦ hsource ⟨hx.1, mem_univ _⟩

theorem shell_subset_target : shell h ⊆ h.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact h.mapsTo (sourceShell_subset_source h hsource hx)

theorem symm_mem_sourceShell {z : V3} (hz : z ∈ shell h) :
    h.symm z ∈ sourceShell := by
  obtain ⟨x, hx, rfl⟩ := hz
  rwa [h.left_inv (sourceShell_subset_source h hsource hx)]



noncomputable def toShell : C(source, shell h) where
  toFun x := ⟨h (coordinates x),
    ⟨coordinates x, coordinates_mem_sourceShell x.property, rfl⟩⟩
  continuous_toFun := (h.continuousOn.comp_continuous
    (coordinates.continuous.comp continuous_subtype_val)
    (fun x ↦ sourceShell_subset_source h hsource
      (coordinates_mem_sourceShell x.property))).subtype_mk _

theorem toShell_apply (x : source) :
    (toShell h hsource x : V3) = h ((x : V1 × V2).1, (3 / 2 : ℝ) • (x : V1 × V2).2) :=
  rfl


noncomputable def rimMap (b : Bool) (u : V2) : V3 := h (endpoint b, (3 / 2 : ℝ) • u)


noncomputable def rim (b : Bool) : C(Q2, shell h) :=
  (toShell h hsource).comp
    ⟨fun u ↦ ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

theorem rim_apply (b : Bool) (u : Q2) :
    (rim h hsource b u : V3) = h (endpoint b, (3 / 2 : ℝ) • (u : V2)) := rfl

theorem toShell_endpoint (b : Bool) (u : Q2) :
    toShell h hsource
      ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩ =
        rim h hsource b u := rfl



theorem exists_rim_homotopy :
    ∃ H : (rim h hsource false).Homotopy (rim h hsource true),
      ∀ (t : unitInterval) (u : Q2),
        (H (t, u) : V3) = h ((fun _ : Fin 1 ↦ 2 * (t : ℝ) - 1),
          (3 / 2 : ℝ) • (u : V2)) := by
  let a : C(unitInterval × Q2, source) := {
    toFun p := ⟨((fun _ : Fin 1 ↦ 2 * (p.1 : ℝ) - 1), p.2), by
      refine ⟨?_, p.2.property⟩
      rw [mem_closedBall, dist_zero_right, pi_norm_const, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩⟩
    continuous_toFun := by fun_prop }
  let H : (rim h hsource false).Homotopy (rim h hsource true) := {
    toContinuousMap := (toShell h hsource).comp a
    map_zero_left := by
      intro u
      apply Subtype.ext
      change h ((fun _ : Fin 1 ↦ 2 * (0 : ℝ) - 1), (3 / 2 : ℝ) • (u : V2)) =
        h (endpoint false, (3 / 2 : ℝ) • (u : V2))
      apply congrArg h
      refine Prod.ext ?_ rfl
      funext i
      change 2 * (0 : ℝ) - 1 = -1
      norm_num
    map_one_left := by
      intro u
      apply Subtype.ext
      change h ((fun _ : Fin 1 ↦ 2 * (1 : ℝ) - 1), (3 / 2 : ℝ) • (u : V2)) =
        h (endpoint true, (3 / 2 : ℝ) • (u : V2))
      apply congrArg h
      refine Prod.ext ?_ rfl
      funext i
      change 2 * (1 : ℝ) - 1 = 1
      norm_num }
  exact ⟨H, fun _ _ ↦ rfl⟩

private theorem transverse_ne_zero (z : shell h) : (h.symm z).2 ≠ 0 := by
  have hz := (symm_mem_sourceShell h hsource z.property).2.1
  intro heq
  rw [heq, norm_zero] at hz
  linarith


noncomputable def radial : C(shell h, Q2) where
  toFun z := ⟨normalize (h.symm z).2, mem_sphere_zero_iff_norm.mpr
    (norm_normalize (transverse_ne_zero h hsource z))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hi : Continuous (fun z : shell h ↦ (h.symm z).2) :=
      continuous_snd.comp (h.symm.continuousOn.comp_continuous continuous_subtype_val
        (fun z ↦ shell_subset_target h hsource z.property))
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ContinuousAt.comp (f := fun z : shell h ↦ (h.symm z).2)
      (continuousAt_normalize_of_ne_zero (transverse_ne_zero h hsource z)) hi.continuousAt

theorem radial_apply (z : shell h) :
    (radial h hsource z : V2) = normalize (h.symm z).2 := rfl

theorem radial_toShell (x : source) :
    (radial h hsource (toShell h hsource x) : V2) = (x : V1 × V2).2 := by
  change normalize (h.symm (h (coordinates x))).2 = _
  rw [h.left_inv (sourceShell_subset_source h hsource
    (coordinates_mem_sourceShell x.property)), coordinates_apply]
  rw [normalize_smul_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp x.property.2)

theorem radial_rim (b : Bool) (u : Q2) : radial h hsource (rim h hsource b u) = u := by
  apply Subtype.ext
  exact radial_toShell h hsource
    ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩


theorem rim_class_ne_one (b : Bool) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map (rim h hsource b).continuous)) ≠ 1 :=
  squareRimLoop_map_class_ne_one_of_retraction (rim h hsource b) (radial h hsource)
    (radial_rim h hsource b)



theorem toShell_isClosedEmbedding : IsClosedEmbedding (toShell h hsource) := by
  let : CompactSpace source := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
  apply (toShell h hsource).continuous.isClosedEmbedding
  intro x y hxy
  have heq := h.injOn
    (sourceShell_subset_source h hsource (coordinates_mem_sourceShell x.property))
    (sourceShell_subset_source h hsource (coordinates_mem_sourceShell y.property))
    (congrArg Subtype.val hxy)
  rw [coordinates_apply, coordinates_apply] at heq
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · have hh := congrArg Prod.fst heq
    exact hh
  · ext i
    have hh := congrFun (congrArg Prod.snd heq) i
    change (3 / 2 : ℝ) * (x : V1 × V2).2 i = (3 / 2 : ℝ) * (y : V1 × V2).2 i at hh
    linarith

theorem rim_isClosedEmbedding (b : Bool) : IsClosedEmbedding (rim h hsource b) := by
  let : CompactSpace Q2 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  exact (rim h hsource b).continuous.isClosedEmbedding
    (Function.LeftInverse.injective (radial_rim h hsource b))

theorem disjoint_rim_ranges : Disjoint (range (rim h hsource false))
    (range (rim h hsource true)) := by
  apply disjoint_left.mpr
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  have hi := (toShell_isClosedEmbedding h hsource).injective hv
  have hh := congrFun (congrArg (fun x : source ↦ (x : V1 × V2).1) hi) 0
  norm_num [endpoint] at hh



theorem toShell_old_boundary_iff (x : source) :
    h.symm (toShell h hsource x) ∈
        frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ↔
      (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  change h.symm (h (coordinates x)) ∈ _ ↔ _
  rw [h.left_inv (sourceShell_subset_source h hsource
    (coordinates_mem_sourceShell x.property))]
  simp only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero, coordinates_apply,
    mem_prod, mem_univ, and_true]



theorem rimMap_finitePL {N : Set (V1 × V2)}
    (hboundary : frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) (b : Bool) :
    FinitePiecewiseAffineOn (rimMap h b) Q2 := by
  let f : V2 →ᴬ[ℝ] (V1 × V2) :=
    (ContinuousAffineMap.const ℝ V2 (endpoint b)).prod
      ((3 / 2 : ℝ) • (ContinuousLinearMap.id ℝ V2)).toContinuousAffineMap
  have hf : FinitePiecewiseAffineOn f Q2 :=
    ⟨squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon,
      squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon,
      (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
        boundary_squareRimPolygon,
      SimplicialComplex.affineOnFaces_affine
        (squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon) f⟩
  apply hPL.comp_finitePiecewiseAffineOn hf
  intro u hu
  refine ⟨hsource ⟨sphere_subset_closedBall (endpoint_mem_sphere b), mem_univ _⟩,
    hboundary ?_⟩
  rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
  exact ⟨endpoint_mem_sphere b, mem_univ _⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
