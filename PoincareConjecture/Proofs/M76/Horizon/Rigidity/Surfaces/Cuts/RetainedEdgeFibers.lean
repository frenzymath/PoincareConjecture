import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.FiberChains
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTrianglePartialQuotient

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E)

omit [FiniteDimensional ℝ E] in

theorem edge_subset_of_mem_openSegment_mem_convexHull
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) {u : Finset E} (hu : u ∈ K.faces)
    (hzu : z ∈ convexHull ℝ (u : Set E)) : ({a, b} : Finset E) ⊆ u := by
  have hze : z ∈ convexHull ℝ (({a, b} : Finset E) : Set E) := by
    simpa only [Finset.coe_pair, convexHull_pair] using openSegment_subset_segment ℝ a b hz
  have hcommon := K.inter_subset_convexHull he hu ⟨hze, hzu⟩
  have hza : z ≠ a := by
    intro h
    subst z
    exact hab (left_mem_openSegment_iff.mp hz)
  have hzb : z ≠ b := by
    intro h
    subst z
    exact hab (right_mem_openSegment_iff.mp hz)
  have ha : a ∈ u := by
    by_contra h
    have hsub : (({a, b} : Finset E) : Set E) ∩ (u : Set E) ⊆ ({b} : Set E) := by
      rintro x ⟨hx, hxu⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (h hxu).elim
      · rfl
    have hz' := convexHull_mono hsub hcommon
    rw [convexHull_singleton] at hz'
    exact hzb hz'
  have hb : b ∈ u := by
    by_contra h
    have hsub : (({a, b} : Finset E) : Set E) ∩ (u : Set E) ⊆ ({a} : Set E) := by
      rintro x ⟨hx, hxu⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact (h hxu).elim
    have hz' := convexHull_mono hsub hcommon
    rw [convexHull_singleton] at hz'
    exact hza hz'
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb

theorem mem_convexHull_iff_edge_subset
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) (u : Triangle K) :
    z ∈ convexHull ℝ (u.val : Set E) ↔ ({a, b} : Finset E) ⊆ u.val := by
  refine ⟨edge_subset_of_mem_openSegment_mem_convexHull K hab he hz u.property.1, ?_⟩
  intro hsub
  apply convexHull_mono (Finset.coe_subset.mpr hsub)
  simpa only [Finset.coe_pair, convexHull_pair] using openSegment_subset_segment ℝ a b hz

theorem fiberTriangle_edge_inventory
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) {s t : Triangle K}
    (hcofaces : ∀ u : Triangle K, ({a, b} : Finset E) ⊆ u.val ↔ u = s ∨ u = t)
    (u : fiberTriangle K z) : u.val = s ∨ u.val = t :=
  (hcofaces u.val).mp ((mem_convexHull_iff_edge_subset K hab he hz u.val).mp u.property)

theorem retained_edge_fiberChain_eq
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) {s t : Triangle K}
    (hcofaces : ∀ u : Triangle K, ({a, b} : Finset E) ⊆ u.val ↔ u = s ∨ u = t)
    (contact : Triangle K → Triangle K → Prop) (hst : ¬ contact s t) (hts : ¬ contact t s)
    {u v : fiberTriangle K z}
    (h : Relation.EqvGen (fun q r : fiberTriangle K z ↦ contact q.val r.val) u v) :
    u = v := by
  have hstep (q r : fiberTriangle K z) (hqr : contact q.val r.val) : q = r := by
    apply Subtype.ext
    rcases fiberTriangle_edge_inventory K hab he hz hcofaces q with hq | hq <;>
      rcases fiberTriangle_edge_inventory K hab he hz hcofaces r with hr | hr
    · exact hq.trans hr.symm
    · exact (hst (hq ▸ hr ▸ hqr)).elim
    · exact (hts (hq ▸ hr ▸ hqr)).elim
    · exact hq.trans hr.symm
  induction h with
  | rel q r hqr => exact hstep q r hqr
  | refl q => rfl
  | symm q r hqr ih => exact ih.symm
  | trans q r w hqr hrw ihqr ihrw => exact ihqr.trans ihrw

theorem partialMk_injective_retained_edge_fiber
    (label : Triangle K → ℝ) (hi : Function.Injective label)
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) {s t : Triangle K}
    (hcofaces : ∀ u : Triangle K, ({a, b} : Finset E) ⊆ u.val ↔ u = s ∨ u = t)
    (contact : Triangle K → Triangle K → Prop) (hst : ¬ contact s t) (hts : ¬ contact t s) :
    Function.Injective (fun u : fiberTriangle K z ↦
      partialMk K label contact (fiberCopy K label z u)) := by
  intro u v huv
  apply retained_edge_fiberChain_eq K hab he hz hcofaces contact hst hts
  apply (fiberCopy_glue_iff K label hi contact u v).mp
  exact (partialQuotient_mk_eq_iff K label contact _ _).mp huv

theorem partialMk_eq_iff_retained_edge
    (label : Triangle K → ℝ) (hi : Function.Injective label)
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) {s t : Triangle K}
    (hcofaces : ∀ u : Triangle K, ({a, b} : Finset E) ⊆ u.val ↔ u = s ∨ u = t)
    (contact : Triangle K → Triangle K → Prop) (hst : ¬ contact s t) (hts : ¬ contact t s)
    {x y : carrier K label} (hx : x.val.1 = z) (hy : y.val.1 = z) :
    partialMk K label contact x = partialMk K label contact y ↔ x = y := by
  refine ⟨fun h ↦ ?_, congrArg (partialMk K label contact)⟩
  have hglue := (partialQuotient_mk_eq_iff K label contact x y).mp h
  obtain ⟨q, hq⟩ := mem_iUnion.mp x.property
  obtain ⟨r, hr⟩ := mem_iUnion.mp y.property
  let u : fiberTriangle K z := ⟨q, hx ▸ ((mem_copy_iff K label q _).mp hq).1⟩
  let v : fiberTriangle K z := ⟨r, hy ▸ ((mem_copy_iff K label r _).mp hr).1⟩
  have huv : u = v := retained_edge_fiberChain_eq K hab he hz hcofaces contact hst hts
    (pointwiseGlueRelation_fiberChain K label hi contact hglue hx hq hr)
  have hqr : q = r := congrArg Subtype.val huv
  apply Subtype.ext
  exact projection_injective_on_copy K label q hq (hqr ▸ hr) (hx.trans hy.symm)

theorem partialMk_ne_of_retained_edge_owners
    (label : Triangle K → ℝ) (hi : Function.Injective label)
    {a b z : E} (hab : a ≠ b) (he : ({a, b} : Finset E) ∈ K.faces)
    (hz : z ∈ openSegment ℝ a b) {s t : Triangle K} (hne : s ≠ t)
    (hcofaces : ∀ u : Triangle K, ({a, b} : Finset E) ⊆ u.val ↔ u = s ∨ u = t)
    (contact : Triangle K → Triangle K → Prop) (hst : ¬ contact s t) (hts : ¬ contact t s)
    {x y : carrier K label} (hx : x.val.1 = z) (hy : y.val.1 = z)
    (hxs : x.val ∈ copy K label s) (hyt : y.val ∈ copy K label t) :
    partialMk K label contact x ≠ partialMk K label contact y := by
  intro h
  have hxy := (partialMk_eq_iff_retained_edge K label hi hab he hz hcofaces
    contact hst hts hx hy).mp h
  have hxt : x.val ∈ copy K label t := hxy ▸ hyt
  exact Set.disjoint_left.mp (disjoint_copies K label hi hne) hxs hxt

end PoincareConjecture.M76.OriginalTriangleCopies
