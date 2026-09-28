import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CommonNeighborhood
import Mathlib.Analysis.Normed.Affine.MazurUlam

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem frame_projection_translate (d : TerminalSaddleGeometry M P p e)
    (y : E3) (t : Real) :
    Saddle.toE2 (d.frame (y + t • (M.v : E3))) = Saddle.toE2 (d.frame y) := by
  let J₀ : E3 ≃ᵢ E3 := { d.frame.toEquiv with isometry_toFun := d.frame_isometry }
  let J := J₀.toRealLinearIsometryEquivOfMapZero d.frame_zero
  have hJ (x : E3) : J x = d.frame x := rfl
  let axis : E3 := EuclideanSpace.single 2 1
  have hJv : J (M.v : E3) = axis := by
    apply ext_inner_right Real
    intro x
    obtain ⟨y, rfl⟩ := J.surjective x
    rw [J.inner_map_map]
    simpa [axis, PiLp.inner_apply, hJ] using (d.frame_height y).symm
  change Saddle.toE2 (J (y + t • (M.v : E3))) = Saddle.toE2 (J y)
  rw [map_add, map_smul, hJv]
  ext i
  fin_cases i <;> simp [Saddle.toE2, axis]

theorem terminal_actual_slice_eq_patch_union_strips
    (d : TerminalSaddleGeometry M P p e) {t : Real} (ht : t ∈ Icc (-d.delta) d.delta) :
    d.A (inner Real (M.v : E3) (g p) + t) =
      (fun x => Saddle.toE2 (d.flatten (g (e x)))) ''
        (closedSquare d.r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
      ⋃ i, (fun s => Saddle.toE2 (d.frame (g (d.strips i (s, 0))))) ''
        Icc (d.a i) (d.b i) := by
  let z := inner Real (M.v : E3) (g p) + t
  have hslice : d.A z = (Saddle.toE2 ∘ d.frame) ''
      ((d.D ∘ g) '' {q | inner Real (M.v : E3) (g q) = z}) := by
    ext x
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, heq⟩
      have hq : inner Real (M.v : E3) (g q) = z := by
        have hh := congrArg (fun y : E3 => y 2) heq
        change d.frame (d.D (g q)) 2 = z at hh
        rwa [d.frame_height, d.D_height] at hh
      refine ⟨d.D (g q), ⟨q, hq, rfl⟩, ?_⟩
      change Saddle.toE2 (d.flatten (g q)) = x
      rw [heq]
      ext i
      fin_cases i <;> rfl
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨g q, mem_range_self q, ?_⟩
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact ((d.frame_height (d.D (g q))).trans (d.D_height _)).trans hq
  rw [hslice, (d.flattened_levels t ht).2.1, image_union, image_image, image_iUnion]
  congr 1
  apply iUnion_congr
  intro i
  rw [image_image]
  apply image_congr
  intro s _
  exact frame_projection_translate d _ t

theorem exists_terminal_stationary_exterior_neighborhood_within
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (V : Set E2) (hV : IsOpen V)
    (hcritical : ∀ x ∈ closedSquare d.r,
      (d.flatten (g (e x))) 2 = inner Real (M.v : E3) (g p) →
        Saddle.toE2 (d.flatten (g (e x))) ∈ V) :
    ∃ δ : Real, 0 < δ ∧ δ ≤ d.delta ∧ ∃ N : Set E2,
      IsOpen N ∧ IsCompact (closure N) ∧ closure N ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        d.A (inner Real (M.v : E3) (g p) + t) ∩ closure N =
          d.B (inner Real (M.v : E3) (g p) + t) ∩ closure N) ∧
      (∀ t ∈ Icc (-δ) δ,
        d.A (inner Real (M.v : E3) (g p) + t) \ closure N =
          d.A (inner Real (M.v : E3) (g p)) \ closure N) ∧
      ∀ t ∈ Icc (-δ) δ, ∀ x ∈ closedSquare d.r,
        -(x 0)^2 + (x 1)^2 = t → Saddle.toE2 (d.flatten (g (e x))) ∈ N := by
  obtain ⟨ε, hε, N, hN, hNc, hNV, hcommon, hpatch⟩ :=
    exists_terminal_common_planar_neighborhood_within hg d d.r_pos d.square_source hsize
      V hV hcritical
  let δ := min ε d.delta
  have hδ : 0 < δ := lt_min hε d.delta_pos
  have hδε : δ ≤ ε := min_le_left _ _
  have hδd : δ ≤ d.delta := min_le_right _ _
  let c := inner Real (M.v : E3) (g p)
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-d.delta) d.delta :=
    ⟨by linarith [ht.1], ht.2.trans hδd⟩
  have hprotected (t : Real) (ht : t ∈ Icc (-δ) δ) (x : E2) (hx : x ∈ closedSquare d.r)
      (hxt : -(x 0)^2 + (x 1)^2 = t) : Saddle.toE2 (d.flatten (g (e x))) ∈ N := by
    apply hpatch x hx
    change d.frame (d.D (g (e x))) 2 ∈ _
    rw [d.frame_height, d.D_height, hform x (d.square_source hx)]
    constructor <;> linarith [ht.1, ht.2]
  have hexterior (t : Real) (ht : t ∈ Icc (-δ) δ) :
      d.A (c + t) \ closure N =
        (⋃ i, (fun s => Saddle.toE2 (d.frame (g (d.strips i (s, 0))))) ''
          Icc (d.a i) (d.b i)) \ closure N := by
    rw [terminal_actual_slice_eq_patch_union_strips d (htime ht)]
    have hsub : (fun x => Saddle.toE2 (d.flatten (g (e x)))) ''
        (closedSquare d.r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ⊆ closure N := by
      rintro _ ⟨x, ⟨hx, hxt⟩, rfl⟩
      exact subset_closure (hprotected t ht x hx hxt)
    rw [union_sdiff_distrib, sdiff_eq_empty.mpr hsub, empty_union]
  refine ⟨δ, hδ, hδd, N, hN, hNc, hNV, ?_, ?_, hprotected⟩
  · intro t ht
    apply hcommon
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht
    simpa only [add_zero] using (hexterior t ht).trans
      (hexterior 0 ⟨by linarith, hδ.le⟩).symm

theorem exists_terminal_stationary_exterior_neighborhood
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ δ : Real, 0 < δ ∧ δ ≤ d.delta ∧ ∃ N : Set E2,
      IsOpen N ∧ IsCompact (closure N) ∧
      (∀ t ∈ Icc (-δ) δ,
        d.A (inner Real (M.v : E3) (g p) + t) ∩ closure N =
          d.B (inner Real (M.v : E3) (g p) + t) ∩ closure N) ∧
      (∀ t ∈ Icc (-δ) δ,
        d.A (inner Real (M.v : E3) (g p) + t) \ closure N =
          d.A (inner Real (M.v : E3) (g p)) \ closure N) ∧
      ∀ t ∈ Icc (-δ) δ, ∀ x ∈ closedSquare d.r,
        -(x 0)^2 + (x 1)^2 = t → Saddle.toE2 (d.flatten (g (e x))) ∈ N := by
  obtain ⟨δ, hδ, hδd, N, hN, hNc, _, hcommon, hstationary, hpatch⟩ :=
    exists_terminal_stationary_exterior_neighborhood_within hg d hsize hform univ isOpen_univ
      (fun _ _ _ => mem_univ _)
  exact ⟨δ, hδ, hδd, N, hN, hNc, hcommon, hstationary, hpatch⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
