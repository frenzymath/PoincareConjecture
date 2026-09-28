import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCircleRegularLevel









set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph




theorem exists_finite_exceptional_circle_values
    {M E ι : Type*} [TopologicalSpace M] [CompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (p : ℝ) [Fact (0 < p)] (q : C(M, AddCircle p))
    (hloc : ∀ x : M, ∃ (i : ι) (K : SimplicialComplex ℝ E) (w : E → ℝ),
      K.faces.Finite ∧ x ∈ (e i).source ∧
      e i x ∈ interior K.space ∧ K.space ⊆ (e i).target ∧
      K.AffineOnFaces w ∧
      ∀ z ∈ K.space, q ((e i).symm z) = (w z : AddCircle p)) :
    ∃ Z : Set (AddCircle p), Z.Finite ∧ ∀ c ∉ Z,
      ∀ x : M, q x = c →
        ∃ (a : ℝ) (ell : E →ᴬ[ℝ] ℝ) (v : E)
          (G : OpenPartialHomeomorph M E),
          (a : AddCircle p) = c ∧ ell.contLinear v = 1 ∧
          x ∈ G.source ∧ ell (G x) = 0 ∧
          (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
          (∀ y ∈ G.source, q y = ((ell (G y) + a : ℝ) : AddCircle p)) ∧
          ∀ y ∈ G.source, q y = c ↔ ell (G y) = 0 := by
  classical
  choose i K w hK hsource hxK _ hfK hlift using hloc
  let V : M → Set M := fun x =>
    (e (i x)).source ∩ (e (i x)) ⁻¹' interior (K x).space
  have hV (x : M) : IsOpen (V x) :=
    (e (i x)).continuousOn_toFun.isOpen_inter_preimage (e (i x)).open_source isOpen_interior
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x, hsource x, hxK x⟩)
  let Z : Set (AddCircle p) := ⋃ x ∈ s,
    (fun z => (w x z : AddCircle p)) '' (K x).vertices
  have hZ : Z.Finite := s.finite_toSet.biUnion fun x _ =>
    ((K x).finite_vertices_of_finite_faces (hK x)).image _
  refine ⟨Z, hZ, ?_⟩
  intro c hc x hxc
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hvalue : (w y (e (i y) x) : AddCircle p) = c := by
    have h := hlift y (e (i y) x) (interior_subset hxy.2)
    rw [(e (i y)).left_inv hxy.1, hxc] at h
    exact h.symm
  have hreg : ∀ z ∈ (K y).vertices, w y z ≠ w y (e (i y) x) := by
    intro z hz heq
    apply hc
    refine mem_iUnion₂.mpr ⟨y, hys, z, hz, ?_⟩
    change (w y z : AddCircle p) = c
    rw [heq]
    exact hvalue
  obtain ⟨a, ell, v, G, ha, hell, hxG, hzero, hG, hqG, hlevel⟩ :=
    exists_centered_circle_height_chart e hcompat p q (i y) (K y)
      (hK y) (w y) (hfK y) hxy.1 hxy.2 (hlift y) hreg
  refine ⟨a, ell, v, G, ha.trans hxc, hell, hxG, hzero, hG, hqG, ?_⟩
  intro z hz
  simpa only [hxc] using hlevel z hz

end OpenPartialHomeomorph

namespace AddCircle




theorem exists_representative_in_interval_avoiding_finite
    (p : ℝ) [Fact (0 < p)] {Z : Set (AddCircle p)} (hZ : Z.Finite)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ p) :
    ∃ t ∈ Ioo a b, (t : AddCircle p) ∉ Z := by
  have hinj : InjOn (fun t : ℝ => (t : AddCircle p)) (Ioo a b) := by
    intro x hx y hy hxy
    have hxI : x ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨ha.trans hx.1.le, by simpa only [zero_add] using hx.2.trans_le hb⟩
    have hyI : y ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨ha.trans hy.1.le, by simpa only [zero_add] using hy.2.trans_le hb⟩
    exact (coe_eq_coe_iff_of_mem_Ico hxI hyI).mp hxy
  obtain ⟨c, ⟨t, ht, rfl⟩, hc⟩ :=
    ((Ioo_infinite hab).image hinj).exists_notMem_finite hZ
  exact ⟨t, ht, hc⟩




theorem exists_two_representatives_avoiding_finite
    (p : ℝ) [Fact (0 < p)] {Z : Set (AddCircle p)} (hZ : Z.Finite) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (a : AddCircle p) ∉ Z ∧ (b : AddCircle p) ∉ Z ∧
      0 < a ∧ a < b ∧ b < p := by
  have hp : 0 < p := Fact.out
  obtain ⟨a, ha, haZ⟩ := exists_representative_in_interval_avoiding_finite p hZ
    (a := p / 4) (b := p / 3) (by linarith) (by linarith) (by linarith)
  obtain ⟨b, hb, hbZ⟩ := exists_representative_in_interval_avoiding_finite p hZ
    (a := 2 * p / 3) (b := 3 * p / 4) (by linarith) (by linarith) (by linarith)
  exact ⟨a, ha, b, hb, haZ, hbZ, by linarith [ha.1],
    by linarith [ha.2, hb.1], by linarith [hb.2]⟩

end AddCircle
