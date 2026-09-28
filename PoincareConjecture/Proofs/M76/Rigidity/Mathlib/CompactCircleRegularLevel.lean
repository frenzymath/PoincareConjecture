import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleHeightChart
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false

open Set Geometry

namespace AddCircle

theorem exists_representative_avoiding_finite (p : ℝ) [Fact (0 < p)]
    {S : Set (AddCircle p)} (hS : S.Finite) :
    ∃ t ∈ Ioo (0 : ℝ) p, (t : AddCircle p) ∉ S := by
  have hinj : InjOn (fun t : ℝ => (t : AddCircle p)) (Ioo 0 p) := by
    intro x hx y hy hxy
    apply (coe_eq_coe_iff_of_mem_Ico (a := 0)
      (show x ∈ Ico 0 (0 + p) by simpa only [zero_add] using ⟨hx.1.le, hx.2⟩)
      (show y ∈ Ico 0 (0 + p) by simpa only [zero_add] using ⟨hy.1.le, hy.2⟩)).mp
    exact hxy
  have hinfinite := (Ioo_infinite (show (0 : ℝ) < p from Fact.out)).image hinj
  obtain ⟨c, ⟨t, ht, rfl⟩, hc⟩ := hinfinite.exists_notMem_finite hS
  exact ⟨t, ht, hc⟩

end AddCircle

namespace OpenPartialHomeomorph

theorem exists_compact_regular_circle_level
    {M E ι : Type*} [TopologicalSpace M] [CompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (p : ℝ) [Fact (0 < p)] (q : C(M, AddCircle p)) (hq : Function.Surjective q)
    (hloc : ∀ x : M, ∃ (i : ι) (K : SimplicialComplex ℝ E) (w : E → ℝ),
      K.faces.Finite ∧ x ∈ (e i).source ∧
      e i x ∈ interior K.space ∧ K.space ⊆ (e i).target ∧
      K.AffineOnFaces w ∧
      ∀ z ∈ K.space, q ((e i).symm z) = (w z : AddCircle p)) :
    ∃ t ∈ Ioo (0 : ℝ) p,
      IsCompact (q ⁻¹' {(t : AddCircle p)}) ∧
      (q ⁻¹' {(t : AddCircle p)}).Nonempty ∧
      ∀ x : M, q x = (t : AddCircle p) →
        ∃ (a : ℝ) (ell : E →ᴬ[ℝ] ℝ) (v : E)
          (G : OpenPartialHomeomorph M E),
          (a : AddCircle p) = (t : AddCircle p) ∧ ell.contLinear v = 1 ∧
          x ∈ G.source ∧ ell (G x) = 0 ∧
          (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
          (∀ y ∈ G.source, q y = ((ell (G y) + a : ℝ) : AddCircle p)) ∧
          ∀ y ∈ G.source, q y = (t : AddCircle p) ↔ ell (G y) = 0 := by
  classical
  choose i K w hK hsource hxK _ hfK hlift using hloc
  let V : M → Set M := fun x =>
    (e (i x)).source ∩ (e (i x)) ⁻¹' interior (K x).space
  have hV (x : M) : IsOpen (V x) :=
    (e (i x)).continuousOn_toFun.isOpen_inter_preimage (e (i x)).open_source isOpen_interior
  have hxV (x : M) : x ∈ V x := ⟨hsource x, hxK x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  let F : Set (AddCircle p) := ⋃ x ∈ s,
    (fun z => (w x z : AddCircle p)) '' (K x).vertices
  have hF : F.Finite := s.finite_toSet.biUnion fun x _ =>
    ((K x).finite_vertices_of_finite_faces (hK x)).image _
  obtain ⟨t, ht, htF⟩ := AddCircle.exists_representative_avoiding_finite p hF
  obtain ⟨x0, hx0⟩ := hq (t : AddCircle p)
  refine ⟨t, ht, (isClosed_singleton.preimage q.continuous).isCompact,
    ⟨x0, hx0⟩, ?_⟩
  intro x hxt
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hvalue : (w y (e (i y) x) : AddCircle p) = (t : AddCircle p) := by
    have h := hlift y (e (i y) x) (interior_subset hxy.2)
    rw [(e (i y)).left_inv hxy.1, hxt] at h
    exact h.symm
  have hreg : ∀ z ∈ (K y).vertices, w y z ≠ w y (e (i y) x) := by
    intro z hz heq
    apply htF
    refine mem_iUnion₂.mpr ⟨y, hys, z, hz, ?_⟩
    change (w y z : AddCircle p) = (t : AddCircle p)
    rw [heq]
    exact hvalue
  obtain ⟨a, ell, v, G, ha, hell, hxG, hzero, hG, hqG, hlevel⟩ :=
    exists_centered_circle_height_chart e hcompat p q (i y) (K y)
      (hK y) (w y) (hfK y) hxy.1 hxy.2 (hlift y) hreg
  refine ⟨a, ell, v, G, ha.trans hxt, hell, hxG, hzero, hG, hqG, ?_⟩
  intro z hz
  simpa only [hxt] using hlevel z hz

end OpenPartialHomeomorph
