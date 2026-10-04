import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.PathClassMap
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.SimplyConnectedCharts
import Mathlib.Topology.Homotopy.Lifting

/-!
# Explicit paths in the path-class cover

The path-class cover of the interval is the interval itself. Functoriality
therefore lifts every path to a path ending at its represented class.
Appending an initial class gives the same endpoint formula for arbitrary
starting points. Source: Hatcher, Section 1.3, printed pp. 63-65; used in
MT Claim 18.16, p. 430.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped unitInterval

universe u

namespace PathClassCover

variable {X : Type u} [TopologicalSpace X] {x y x₀ : X}

private instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, le_rfl, zero_le_one⟩

/-- Equality of endpoints and of dependent path classes gives equality in
the cover. Source: Hatcher, Section 1.3, printed p. 64. -/
@[ext] theorem ext {a b : PathClassCover x₀} (h : a.endpoint = b.endpoint)
    (hc : HEq a.pathClass b.pathClass) : a = b := by
  cases a
  cases b
  cases h
  cases eq_of_heq hc
  rfl

/-- Equal choices of the original basepoint give identical path-class covers.
Source: Hatcher, Section 1.3, printed p. 64. -/
def basepointCongr (h : x = y) : PathClassCover x ≃ₜ PathClassCover y := by
  subst y
  exact Homeomorph.refl _

/-- Changing the original basepoint by equality does not change endpoints.
Source: Hatcher, Section 1.3, printed p. 64. -/
@[simp] theorem basepointCongr_endpoint (h : x = y) (a : PathClassCover x) :
    (basepointCongr h a).endpoint = a.endpoint := by
  subst y
  rfl

/-- Equality transport preserves the constant class point.
Source: Hatcher, Section 1.3, printed p. 64. -/
@[simp] theorem basepointCongr_basepoint (h : x = y) :
    basepointCongr h (basepoint x) = basepoint y := by
  subst y
  rfl

/-- On represented paths equality transport is the usual source cast.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem basepointCongr_mk_path (h : x = y) {z : X} (p : Path x z) :
    basepointCongr h ⟨z, .mk p⟩ = ⟨z, .mk (p.cast h.symm rfl)⟩ := by
  subst y
  rfl

private theorem interval_zero :
    (endpointHomeomorph (0 : I)).symm 0 = basepoint 0 := by
  apply (endpointHomeomorph (0 : I)).injective
  simp [basepoint]

private theorem interval_one :
    (endpointHomeomorph (0 : I)).symm 1 = ⟨1, .mk Path.id⟩ := by
  apply (endpointHomeomorph (0 : I)).injective
  simp

/-- The canonical lift from the constant class ends at the class of the
original path. Source: Hatcher, Section 1.3, printed p. 64. -/
noncomputable def pathFromBase (p : Path x y) :
    Path (basepoint x) (⟨y, .mk p⟩ : PathClassCover x) where
  toFun t := basepointCongr p.source
    (map p.toContinuousMap ((endpointHomeomorph (0 : I)).symm t))
  continuous_toFun := (basepointCongr p.source).continuous.comp
    ((continuous_map p.toContinuousMap).comp (endpointHomeomorph (0 : I)).symm.continuous)
  source' := by
    rw [interval_zero, map_basepoint]
    exact basepointCongr_basepoint p.source
  target' := by
    rw [interval_one]
    change basepointCongr p.source
      ⟨p 1, .mk (Path.id.map p.continuous)⟩ = ⟨y, .mk p⟩
    rw [basepointCongr_mk_path]
    exact ext p.target (Path.Homotopic.hpath_hext (fun _ => rfl))

/-- The canonical lift projects pointwise to the original path.
Source: Hatcher, Section 1.3, printed p. 64. -/
@[simp] theorem endpoint_pathFromBase (p : Path x y) (t : I) :
    (pathFromBase p t).endpoint = p t := by
  change (basepointCongr p.source
    (map p.toContinuousMap ((endpointHomeomorph (0 : I)).symm t))).endpoint = p t
  rw [basepointCongr_endpoint]
  change p ((endpointHomeomorph (0 : I)).symm t).endpoint = p t
  rw [← endpointHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- Prefixing a path class changes the original basepoint of the cover.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
noncomputable def append (a : PathClassCover x₀) (b : PathClassCover a.endpoint) :
    PathClassCover x₀ :=
  ⟨b.endpoint, a.pathClass.trans b.pathClass⟩

/-- Prefixing the constant class returns the prefix point.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
@[simp] theorem append_basepoint (a : PathClassCover x₀) : append a (basepoint a.endpoint) = a := by
  cases a
  simp [append, basepoint]

/-- Prefixing classes preserves local sheet membership.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem append_mem_sheet (a : PathClassCover x₀) {U : Set X}
    {b c : PathClassCover a.endpoint} (hc : c ∈ sheet U b) :
    append a c ∈ sheet U (append a b) := by
  obtain ⟨p, hp, he⟩ := hc
  refine ⟨p, hp, ?_⟩
  change a.pathClass.trans c.pathClass = (a.pathClass.trans b.pathClass).trans (.mk p)
  simp [he]

/-- Prefixing a class is continuous for the sheet topology.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem continuous_append [LocallySimplyConnectedSpace X] (a : PathClassCover x₀) :
    Continuous (append a) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨U, b, hU, hscU, hb, rfl⟩
  apply (isTopologicalBasis a.endpoint).isOpen_iff.mpr
  intro c hc
  have hcU : c.endpoint ∈ U := by
    exact endpoint_mem_of_mem_sheet (a := b) (b := append a c) hc
  refine ⟨sheet U c, ⟨U, c, hU, hscU, hcU, rfl⟩, mem_sheet_self c hcU, ?_⟩
  intro d hd
  change append a d ∈ sheet U b
  rw [← sheet_eq_of_mem (show append a c ∈ sheet U b from hc)]
  exact append_mem_sheet a hd

/-- The path-class cover is path connected: each class is reached by its
representative. Source: Hatcher, Section 1.3, printed p. 64. -/
instance pathConnectedSpace (x₀ : X) : PathConnectedSpace (PathClassCover x₀) where
  nonempty := ⟨basepoint x₀⟩
  joined a b := by
    obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective a.pathClass
    obtain ⟨q, hq⟩ := Path.Homotopic.Quotient.mk_surjective b.pathClass
    have ha : (⟨a.endpoint, .mk p⟩ : PathClassCover x₀) = a := ext rfl (heq_of_eq hp)
    have hb : (⟨b.endpoint, .mk q⟩ : PathClassCover x₀) = b := ext rfl (heq_of_eq hq)
    exact ⟨((pathFromBase p).symm.trans (pathFromBase q)).cast ha.symm hb.symm⟩

end PathClassCover
