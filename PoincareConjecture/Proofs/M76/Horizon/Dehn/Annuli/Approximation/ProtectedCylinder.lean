import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.General.ControlledRelativeFinitePLApproximation
import PoincareConjecture.Proofs.M76.RelativeApproximation.Mathlib.CompactRelativeNeighborhood

set_option autoImplicit false

open Set Metric Geometry Topology
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finitePL_cylinder
    (h : OpenPartialHomeomorph (V1 × V2) V3)
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {N : Set (V1 × V2)} (hN : IsOpen N)
    (hboundary : frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    ∃ g : (V1 × V2) → V3, FinitePiecewiseAffineOn g source ∧
      MapsTo g source (shell h) ∧
      (∀ x ∈ sphere (0 : V1) 1 ×ˢ sphere (0 : V2) 1, g x = h (coordinates x)) ∧
      ∃ H : C(unitInterval × source, shell h),
        (∀ x : source, H (0, x) = toShell h hsource x) ∧
        (∀ x : source, (H (1, x) : V3) = g x) ∧
        (∀ (t : unitInterval) (x : source), (x : V1 × V2).1 ∈ sphere (0 : V1) 1 →
          (H (t, x) : V3) = h (coordinates x)) ∧
        ∀ (t : unitInterval) (x : source),
          h.symm (H (t, x)) ∈
              frontier (closedBall (0 : V1) 1 ×ˢ (univ : Set V2)) ↔
            (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  classical
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
  let Z : Set K.space := {x | (x : V1 × V2).1 ∈ sphere (0 : V1) 1}
  let O : Set K.space := {x | coordinates (x : V1 × V2) ∈ h.source ∩ N}
  have hZ : IsCompact Z :=
    (isClosed_sphere.preimage (continuous_fst.comp continuous_subtype_val)).isCompact
  have hO : IsOpen O := (h.open_source.inter hN).preimage
    (coordinates.continuous.comp continuous_subtype_val)
  have hZO : Z ⊆ O := by
    intro x hx
    refine ⟨sourceShell_subset_source h hsource
      (coordinates_mem_sourceShell (hKs ▸ x.property)), hboundary ?_⟩
    rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    exact ⟨hx, mem_univ _⟩
  obtain ⟨L, V, hL, hLK, hV, hZV, hVL, hLO⟩ :=
    K.exists_compact_relative_polyhedral_neighborhood hK hZ hO hZO
  let B : Set (V1 × V2) := Subtype.val '' Vᶜ
  have hB : IsCompact B := hV.isClosed_compl.isCompact.image continuous_subtype_val
  have hBK : B ⊆ K.space := by rintro x ⟨y, _, rfl⟩; exact y.property
  have hBoff (x : V1 × V2) (hx : x ∈ B) : x.1 ∉ sphere (0 : V1) 1 := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact fun hz ↦ hy (hZV hz)
  let a : (V1 × V2) → V3 := h ∘ coordinates
  have hcoords : MapsTo coordinates K.space h.source := by
    intro x hx
    exact sourceShell_subset_source h hsource (coordinates_mem_sourceShell (hKs ▸ hx))
  have ha : ContinuousOn a K.space :=
    h.continuousOn.comp coordinates.continuous.continuousOn hcoords
  have haPL : FinitePiecewiseAffineOn a L.space :=
    hPL.comp_finitePiecewiseAffineOn
      ((L.affineOnFaces_affine coordinates.toContinuousAffineMap).finitePiecewiseAffineOn hL)
      (fun x hx ↦ hLO (show (⟨x, hLK hx⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hx))
  let core : Set (V1 × V2) :=
    ball (0 : V1) 1 ×ˢ {y : V2 | 1 < ‖y‖ ∧ ‖y‖ < 2}
  have hcore : IsOpen core := isOpen_ball.prod
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  have hcoreSource : core ⊆ h.source := by
    intro x hx
    exact hsource ⟨ball_subset_closedBall hx.1, mem_univ _⟩
  have hcoreShell : core ⊆ sourceShell := fun _ hx ↦
    ⟨ball_subset_closedBall hx.1, hx.2⟩
  have haCore : MapsTo a B (h '' core) := by
    intro x hx
    have hxs : x ∈ source := hKs ▸ hBK hx
    have hxne : ‖x.1‖ ≠ 1 := fun heq ↦ hBoff x hx (mem_sphere_zero_iff_norm.mpr heq)
    have hxlt : ‖x.1‖ < 1 := lt_of_le_of_ne
      (mem_closedBall_zero_iff.mp hxs.1) hxne
    refine ⟨coordinates x, ⟨?_, (coordinates_mem_sourceShell hxs).2⟩, rfl⟩
    exact mem_ball_zero_iff.mpr hxlt
  have haTarget : MapsTo a K.space h.target := fun _ hx ↦ h.map_source (hcoords hx)
  obtain ⟨g, hg, hfix, hsegment, hcontrol⟩ :=
    K.exists_relative_finitePL_approximation_with_compact_control hK ha hLK haPL
      h.open_target haTarget hB hBK (h.isOpen_image_of_subset_source hcore hcoreSource) haCore
  let j : source → K.space := fun x ↦ ⟨x, hKs.symm ▸ x.property⟩
  have hsplit (x : source) : (x : V1 × V2) ∈ L.space ∨ (x : V1 × V2) ∈ B := by
    by_cases hx : j x ∈ V
    · exact Or.inl (hVL (mem_image_of_mem Subtype.val hx))
    · exact Or.inr ⟨j x, hx, rfl⟩
  let value : unitInterval × source → V3 := fun z ↦
    (1 - (z.1 : ℝ)) • a z.2 + (z.1 : ℝ) • g z.2
  have hvalueSegment (t : unitInterval) (x : source) :
      value (t, x) ∈ segment ℝ (a x) (g x) := by
    exact ⟨1 - (t : ℝ), (t : ℝ), by linarith [t.property.2], t.property.1, by ring, rfl⟩
  have hvalueFix (t : unitInterval) (x : source) (hx : (x : V1 × V2) ∈ L.space) :
      value (t, x) = a x := by
    change (1 - (t : ℝ)) • a x + (t : ℝ) • g x = a x
    rw [hfix hx, ← add_smul]
    simp
  have hvalueShell (z : unitInterval × source) : value z ∈ shell h := by
    rcases hsplit z.2 with hx | hx
    · rw [hvalueFix z.1 z.2 hx]
      exact ⟨coordinates z.2, coordinates_mem_sourceShell z.2.property, rfl⟩
    · exact image_mono hcoreShell (hcontrol z.2 hx (hvalueSegment z.1 z.2))
  have hvalueContinuous : Continuous value := by
    have hac : Continuous (fun x : source ↦ a x) :=
      (hKs ▸ ha).comp_continuous continuous_subtype_val (fun x ↦ x.property)
    have hgc : Continuous (fun x : source ↦ g x) :=
      (hKs ▸ hg.continuousOn).comp_continuous continuous_subtype_val (fun x ↦ x.property)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hac.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (hgc.comp continuous_snd))
  let H : C(unitInterval × source, shell h) :=
    ⟨fun z ↦ ⟨value z, hvalueShell z⟩, hvalueContinuous.subtype_mk _⟩
  have hvalueOne (x : source) : value (1, x) = g x := by simp [value]
  have hboundaryFix (t : unitInterval) (x : source)
      (hx : (x : V1 × V2).1 ∈ sphere (0 : V1) 1) : value (t, x) = a x :=
    hvalueFix t x (hVL (mem_image_of_mem Subtype.val (hZV (show j x ∈ Z from hx))))
  refine ⟨g, hKs ▸ hg, ?_, ?_, H, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hvalueOne ⟨x, hx⟩ ▸ hvalueShell (1, ⟨x, hx⟩)
  · intro x hx
    let x' : source := ⟨x, sphere_subset_closedBall hx.1, hx.2⟩
    exact (hvalueOne x').symm.trans (hboundaryFix 1 x' hx.1)
  · intro x
    apply Subtype.ext
    change value (0, x) = a x
    simp [value]
  · exact hvalueOne
  · exact hboundaryFix
  · intro t x
    by_cases hx : (x : V1 × V2).1 ∈ sphere (0 : V1) 1
    · change h.symm (value (t, x)) ∈ _ ↔ _
      rw [hboundaryFix t x hx]
      exact toShell_old_boundary_iff h hsource x
    · have hvalueCore : value (t, x) ∈ h '' core := by
        rcases hsplit x with hxl | hxb
        · rw [hvalueFix t x hxl]
          have hxlt : ‖(x : V1 × V2).1‖ < 1 := lt_of_le_of_ne
            (mem_closedBall_zero_iff.mp x.property.1)
            (fun heq ↦ hx (mem_sphere_zero_iff_norm.mpr heq))
          exact ⟨coordinates x,
            ⟨mem_ball_zero_iff.mpr hxlt, (coordinates_mem_sourceShell x.property).2⟩, rfl⟩
        · exact hcontrol x hxb (hvalueSegment t x)
      obtain ⟨y, hy, hyvalue⟩ := hvalueCore
      change h.symm (value (t, x)) ∈ _ ↔ _
      rw [← hyvalue, h.left_inv (hcoreSource hy)]
      simp only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero, mem_prod,
        mem_univ, and_true]
      exact iff_of_false (fun hs ↦ (ne_of_lt (mem_ball_zero_iff.mp hy.1))
        (mem_sphere_zero_iff_norm.mp hs)) hx

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
