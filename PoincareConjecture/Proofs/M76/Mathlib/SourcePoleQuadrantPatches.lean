import PoincareConjecture.Proofs.M76.Mathlib.SourcePoleFrontierPatches
import PoincareConjecture.Proofs.M76.Mathlib.SourceQuadrantPatchIncidence












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes RectangleCornerArcs

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





structure SourcePoleQuadrantData (ψ : (ℝ × ℝ) → E) (F S g : Set E)
    (p q : E) (A : E →ₗ[ℝ] ℝ) (t z : ℝ) : Prop where
  disk : IsFinitePLBallPair (ℝ × ℝ) (ψ '' (uIcc 0 t ×ˢ uIcc 0 z))
    ((ψ '' cornerArc 0 t 0 z) ∪ (ψ '' cornerArc t 0 z 0))
  inner : IsFinitePLBallPair ℝ (ψ '' cornerArc 0 t 0 z) {ψ (0, z), ψ (t, 0)}
  outer : IsFinitePLBallPair ℝ (ψ '' cornerArc t 0 z 0) {ψ (0, z), ψ (t, 0)}
  corner_inter : (ψ '' cornerArc 0 t 0 z) ∩ (ψ '' cornerArc t 0 z 0) =
    {ψ (0, z), ψ (t, 0)}
  vertical : IsFinitePLBallPair ℝ (ψ '' ({0} ×ˢ uIcc 0 z)) {p, ψ (0, z)}
  horizontal : IsFinitePLBallPair ℝ (ψ '' (uIcc 0 t ×ˢ {0})) {p, ψ (t, 0)}
  axes_inter : (ψ '' ({0} ×ˢ uIcc 0 z)) ∩ (ψ '' (uIcc 0 t ×ˢ {0})) = {p}
  carrier_subset : ψ '' (uIcc 0 t ×ˢ uIcc 0 z) ⊆ F
  graph_contact : (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ∩ g = ψ '' cornerArc 0 t 0 z
  vertical_subset : ψ '' ({0} ×ˢ uIcc 0 z) ⊆ F ∩ {x | A x = 0}
  horizontal_subset : ψ '' (uIcc 0 t ×ˢ {0}) ⊆ F ∩ S
  vertical_endpoint : ψ (0, z) ∈ ((ψ '' ({0} ×ˢ uIcc 0 z)) ∩ g) \ {p, q}
  horizontal_endpoint : ψ (t, 0) ∈ ((ψ '' (uIcc 0 t ×ˢ {0})) ∩ g) \ {p, q}
  endpoint_ne : ψ (0, z) ≠ ψ (t, 0)
  outer_off_graph : (ψ '' cornerArc t 0 z 0) \ {ψ (0, z), ψ (t, 0)} ⊆ gᶜ
  other_notMem : q ∉ ψ '' (uIcc 0 t ×ˢ uIcc 0 z)
  vertical_other_notMem : q ∉ ψ '' ({0} ×ˢ uIcc 0 z)
  horizontal_other_notMem : q ∉ ψ '' (uIcc 0 t ×ˢ {0})






theorem FinitePiecewiseAffineOn.source_pole_quadrant_data
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {r : ℝ}
    (hψ : FinitePiecewiseAffineOn ψ (base r)) (hinj : Function.Injective ψ)
    (hψzero : ψ 0 = p) (hr : 0 < r) (hq : q ∉ ψ '' base r)
    (A : E →ₗ[ℝ] ℝ) (hgraph : g = F ∩ (S ∪ {x | A x = 0}))
    (hfront : ψ '' base r ⊆ F) (hheight : ∀ x : ℝ × ℝ, A (ψ x) = x.1)
    (hsurface : ∀ x ∈ base r, ψ x ∈ S ↔ x.2 = 0)
    {t z : ℝ} (ht : t ≠ 0) (hz : z ≠ 0) (htr : |t| ≤ r) (hzr : |z| ≤ r) :
    SourcePoleQuadrantData ψ F S g p q A t z := by
  have hzero : (0 : ℝ × ℝ) ∈ base r :=
    ⟨⟨neg_nonpos.mpr hr.le, hr.le⟩, neg_nonpos.mpr hr.le, hr.le⟩
  have hrect : (uIcc 0 t ×ˢ uIcc 0 z) ⊆ base r :=
    prod_mono (uIcc_subset_Icc ⟨neg_nonpos.mpr hr.le, hr.le⟩ (abs_le.mp htr))
      (uIcc_subset_Icc ⟨neg_nonpos.mpr hr.le, hr.le⟩ (abs_le.mp hzr))
  have hrectF : ψ '' (uIcc 0 t ×ˢ uIcc 0 z) ⊆ F :=
    (image_mono hrect).trans hfront
  have hrectS (x : ℝ × ℝ) (hx : x ∈ uIcc 0 t ×ˢ uIcc 0 z) :
      ψ x ∈ S ↔ x.2 = 0 := hsurface x (hrect hx)
  have hmarks : ({p} : Set E) ⊆ S ∩ {x | A x = 0} := by
    intro x hx
    have hxp : x = p := hx
    rw [hxp]
    refine ⟨hψzero ▸ (hsurface 0 hzero).mpr rfl, ?_⟩
    change A p = 0
    rw [← hψzero, hheight]
    rfl
  obtain ⟨hd, hu, hw, huw⟩ := hψ.rectangle_corner_patches hinj ht.symm hz.symm hrect
  obtain ⟨hv, hh, hvh⟩ := hψ.quadrant_axis_intervals hinj ht hz hrect
  obtain ⟨hvF, hhF, hvend, hhend, houter⟩ :=
    quadrant_axis_incidence_of_height_surface hinj A ht hz hgraph hrectF
      hheight hrectS hmarks
  have hvD : ψ '' ({0} ×ˢ uIcc 0 z) ⊆ ψ '' (uIcc 0 t ×ˢ uIcc 0 z) := by
    apply image_mono
    rintro x ⟨hx, hy⟩
    exact ⟨hx ▸ left_mem_uIcc, hy⟩
  have hhD : ψ '' (uIcc 0 t ×ˢ {0}) ⊆ ψ '' (uIcc 0 t ×ˢ uIcc 0 z) := by
    apply image_mono
    rintro x ⟨hx, hy⟩
    exact ⟨hx, hy ▸ left_mem_uIcc⟩
  have hqD : q ∉ ψ '' (uIcc 0 t ×ˢ uIcc 0 z) := fun hx => hq (image_mono hrect hx)
  have hqV : q ∉ ψ '' ({0} ×ˢ uIcc 0 z) := fun hx => hqD (hvD hx)
  have hqH : q ∉ ψ '' (uIcc 0 t ×ˢ {0}) := fun hx => hqD (hhD hx)
  refine {
    disk := hd
    inner := hu
    outer := hw
    corner_inter := huw
    vertical := by simpa only [hψzero] using hv
    horizontal := by simpa only [hψzero] using hh
    axes_inter := by simpa only [hψzero] using hvh
    carrier_subset := hrectF
    graph_contact := quadrant_graph_contact_of_height_surface A hgraph hrectF hheight hrectS
    vertical_subset := hvF
    horizontal_subset := hhF
    vertical_endpoint := ⟨hvend.1, ?_⟩
    horizontal_endpoint := ⟨hhend.1, ?_⟩
    endpoint_ne := ?_
    outer_off_graph := houter
    other_notMem := hqD
    vertical_other_notMem := hqV
    horizontal_other_notMem := hqH }
  · rintro (heq | heq)
    · exact hvend.2 heq
    · exact hqV (heq ▸ hvend.1.1)
  · rintro (heq | heq)
    · exact hhend.2 heq
    · exact hqH (heq ▸ hhend.1.1)
  · intro heq
    exact ht (congrArg Prod.fst (hinj heq)).symm




theorem source_pole_opposite_axis_contacts
    {ψ : (ℝ × ℝ) → E} (hinj : Function.Injective ψ) {p : E}
    (hψzero : ψ 0 = p) {r : ℝ} (hr : 0 ≤ r) :
    (ψ '' ({0} ×ˢ uIcc 0 (-r))) ∩ (ψ '' ({0} ×ˢ uIcc 0 r)) = {p} ∧
    (ψ '' (uIcc 0 (-r) ×ˢ {0})) ∩ (ψ '' (uIcc 0 r ×ˢ {0})) = {p} := by
  have hv : ({(0 : ℝ)} ×ˢ uIcc 0 (-r)) ∩ ({0} ×ˢ uIcc 0 r) = {(0 : ℝ × ℝ)} := by
    rw [uIcc_of_ge (neg_nonpos.mpr hr), uIcc_of_le hr]
    ext x
    constructor
    · rintro ⟨⟨hx, _, hx0⟩, _, h0x, _⟩
      exact Prod.ext hx (le_antisymm hx0 h0x)
    · rintro rfl
      exact ⟨⟨rfl, neg_nonpos.mpr hr, le_rfl⟩, rfl, le_rfl, hr⟩
  have hh : (uIcc 0 (-r) ×ˢ {(0 : ℝ)}) ∩ (uIcc 0 r ×ˢ {0}) = {(0 : ℝ × ℝ)} := by
    rw [uIcc_of_ge (neg_nonpos.mpr hr), uIcc_of_le hr]
    ext x
    constructor
    · rintro ⟨⟨⟨_, hx0⟩, hx⟩, ⟨h0x, _⟩, _⟩
      exact Prod.ext (le_antisymm hx0 h0x) hx
    · rintro rfl
      exact ⟨⟨⟨neg_nonpos.mpr hr, le_rfl⟩, rfl⟩, ⟨le_rfl, hr⟩, rfl⟩
  constructor
  · rw [← image_inter hinj, hv, image_singleton, hψzero]
  · rw [← image_inter hinj, hh, image_singleton, hψzero]

end Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_source_pole_quadrant_patches
    {C S : Set E} (H : Finset (E →ₗ[ℝ] ℝ))
    (hC : C = {x | ∀ A ∈ H, A x ≤ 1})
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) (A : E →ₗ[ℝ] ℝ)
    (hheight : ∀ x : E, (e x).1.1 = A x)
    {p q : E} (hp : p ∈ frontier C) (hpq : p ≠ q) {σ : ℝ} (hσ : σ ≠ 0)
    (hep : e p = ((0, σ), 0))
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    (hS : ∀ x ∈ U, x ∈ S ↔ (e x).2 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : (ℝ × ℝ) → ℝ) (ψ : (ℝ × ℝ) → E) (V : Set E) (r : ℝ),
      Continuous f ∧ f 0 = 1 ∧ Continuous ψ ∧ Function.Injective ψ ∧
      ψ 0 = p ∧ IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ q ∉ V ∧ r ∈ Ioo 0 ε ∧
      FinitePiecewiseAffineOn ψ (base r) ∧ ψ '' base r ⊆ frontier C ∩ V ∧
      (∀ x, e (ψ x) = ((x.1, σ * f x), x.2)) ∧
      (∀ x, A (ψ x) = x.1) ∧
      (∀ x ∈ base r, ψ x ∈ S ↔ x.2 = 0) ∧
      IsFinitePLBallPair (ℝ × ℝ) (ψ '' base r) (ψ '' baseBoundary r) ∧
      (∀ T ⊆ base r,
        (frontier C ∩ V) ∩ (fun x => ((e x).1.1, (e x).2)) ⁻¹' T = ψ '' T) ∧
      (∃ O : Set E, IsOpen O ∧ p ∈ O ∧ frontier C ∩ O ⊆ ψ '' base r) ∧
      ∀ t z : ℝ, t ≠ 0 → z ≠ 0 → |t| ≤ r → |z| ≤ r →
        SourcePoleQuadrantData ψ (frontier C) S (frontier C ∩ (S ∪ {x | A x = 0}))
          p q A t z := by
  have hpU' : p ∈ U ∩ ({q} : Set E)ᶜ := ⟨hpU, hpq⟩
  obtain ⟨f, ψ, V, r, hf, hfzero, hψ, hinj, hψzero, hV, hpV, hVU, hr,
    hψPL, hψbase, hcoords, hψheight, hψsurface, hball, hactual, hneighbor⟩ :=
    exists_source_pole_frontier_patch H hC e A hheight hp hσ hep
      (hU.inter isClosed_singleton.isOpen_compl) hpU'
      (fun x hx => hS x hx.1) hε
  have hqV : q ∉ V := fun hx => (hVU hx).2 rfl
  have hqbase : q ∉ ψ '' base r := fun hx => hqV (hψbase hx).2
  refine ⟨f, ψ, V, r, hf, hfzero, hψ, hinj, hψzero, hV, hpV,
    fun x hx => (hVU hx).1, hqV, hr, hψPL, hψbase, hcoords, hψheight,
    hψsurface, hball, hactual, hneighbor, ?_⟩
  intro t z ht hz htr hzr
  exact hψPL.source_pole_quadrant_data hinj hψzero hr.1 hqbase A rfl
    (fun x hx => (hψbase hx).1) hψheight hψsurface ht hz htr hzr

end Geometry.SimplicialComplex
