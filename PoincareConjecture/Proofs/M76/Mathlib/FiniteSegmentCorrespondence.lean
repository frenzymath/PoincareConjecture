import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F ι V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
  [DecidableEq E] [DecidableEq F]

theorem exists_finite_segment_complex (a b : ι → E) (hne : ∀ i, a i ≠ b i)
    (hinter : ∀ i j, segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j) ⊆
      convexHull ℝ (({a i, b i} : Set E) ∩ {a j, b j})) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧
      (∀ s : Finset E, s ∈ K.faces ↔ s.Nonempty ∧ ∃ i, s ⊆ {a i, b i}) ∧
      K.space = ⋃ i, segment ℝ (a i) (b i) := by
  classical
  let e : ι → Finset E := fun i => {a i, b i}
  have hind : ∀ s ∈ range e, AffineIndependent ℝ ((↑) : s → E) := by
    rintro _ ⟨i, rfl⟩
    change AffineIndependent ℝ ((↑) : ↥(e i : Set E) → E)
    rw [show (e i : Set E) = {a i, b i} by simp only [e, Finset.coe_pair]]
    have h := (affineIndependent_of_ne ℝ (hne i)).range
    rw [Matrix.range_cons_cons_empty] at h
    exact h
  have hgeom : ∀ s ∈ range e, ∀ t ∈ range e,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    simpa only [e, Finset.coe_pair, convexHull_pair] using hinter i j
  refine ⟨ofGenerators (range e) hind hgeom,
    finite_ofGenerators_faces (finite_range e) hind hgeom, ?_, ?_⟩
  · intro s
    change (s.Nonempty ∧ ∃ t ∈ range e, s ⊆ t) ↔ _
    constructor
    · rintro ⟨hs, _, ⟨i, rfl⟩, hsi⟩
      exact ⟨hs, i, hsi⟩
    · rintro ⟨hs, i, hsi⟩
      exact ⟨hs, e i, mem_range_self i, hsi⟩
  · rw [space_ofGenerators, biUnion_range]
    simp only [e, Finset.coe_pair, convexHull_pair]

omit [Finite ι] in
private theorem vertices_eq_range_of_edge_labels (K : SimplicialComplex ℝ E)
    (a b : ι → V) (p : V → E)
    (hcover : ∀ v, ∃ i, v = a i ∨ v = b i)
    (hfaces : ∀ s : Finset E, s ∈ K.faces ↔
      s.Nonempty ∧ ∃ i, s ⊆ {p (a i), p (b i)}) : K.vertices = range p := by
  classical
  ext x
  change ({x} : Finset E) ∈ K.faces ↔ _
  rw [hfaces]
  simp only [Finset.singleton_nonempty, true_and, Finset.singleton_subset_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl | rfl⟩ <;> exact mem_range_self _
  · rintro ⟨v, rfl⟩
    obtain ⟨i, rfl | rfl⟩ := hcover v
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩

omit [Finite ι] in
private theorem preserves_edge_label_faces (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (a b : ι → V) (p : V → E) (q : V → F)
    (hK : ∀ s : Finset E, s ∈ K.faces ↔
      s.Nonempty ∧ ∃ i, s ⊆ {p (a i), p (b i)})
    (hL : ∀ s : Finset F, s ∈ L.faces ↔
      s.Nonempty ∧ ∃ i, s ⊆ {q (a i), q (b i)})
    (v : E → F) (hv : ∀ x, v (p x) = q x) :
    ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F) := by
  classical
  intro s hs
  obtain ⟨_, i, hsi⟩ := (hK s).mp hs
  refine ⟨{q (a i), q (b i)}, (hL _).mpr
    ⟨Finset.insert_nonempty _ _, i, Finset.Subset.refl _⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases Finset.mem_insert.mp (hsi hx) with rfl | hx
  · rw [hv]
    exact Finset.mem_insert_self _ _
  · rw [Finset.mem_singleton.mp hx, hv]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [Nonempty V]

omit [DecidableEq E] [DecidableEq F] in

theorem exists_finitePL_segment_correspondence (a b : ι → V)
    (hne : ∀ i, a i ≠ b i) (hcover : ∀ v, ∃ i, v = a i ∨ v = b i)
    (p : V → E) (q : V → F) (hp : Function.Injective p) (hq : Function.Injective q)
    (hpinter : ∀ i j, segment ℝ (p (a i)) (p (b i)) ∩
      segment ℝ (p (a j)) (p (b j)) ⊆
        convexHull ℝ (({p (a i), p (b i)} : Set E) ∩ {p (a j), p (b j)}))
    (hqinter : ∀ i j, segment ℝ (q (a i)) (q (b i)) ∩
      segment ℝ (q (a j)) (q (b j)) ⊆
        convexHull ℝ (({q (a i), q (b i)} : Set F) ∩ {q (a j), q (b j)})) :
    ∃ (f : E → F)
      (e : (⋃ i, segment ℝ (p (a i)) (p (b i))) ≃ₜ
        (⋃ i, segment ℝ (q (a i)) (q (b i)))),
      e.IsFinitePL ∧ (∀ v, f (p v) = q v) ∧
        ∀ x, (e x : F) = f x := by
  classical
  obtain ⟨K, hK, hKface, hKs⟩ := exists_finite_segment_complex
    (p ∘ a) (p ∘ b) (fun i => hp.ne (hne i)) hpinter
  obtain ⟨L, _, hLface, hLs⟩ := exists_finite_segment_complex
    (q ∘ a) (q ∘ b) (fun i => hq.ne (hne i)) hqinter
  have hKv := vertices_eq_range_of_edge_labels K a b p hcover hKface
  have hLv := vertices_eq_range_of_edge_labels L a b q hcover hLface
  let v : E → F := fun x => q (Function.invFun p x)
  let w : F → E := fun y => p (Function.invFun q y)
  have hv (x : V) : v (p x) = q x := congrArg q (Function.leftInverse_invFun hp x)
  have hw (x : V) : w (q x) = p x := congrArg p (Function.leftInverse_invFun hq x)
  obtain ⟨f, _, H, hf, _, hfv, _, hH, _⟩ :=
    K.exists_homeomorph_of_vertex_maps L hK v w
      (preserves_edge_label_faces K L a b p q hKface hLface v hv)
      (preserves_edge_label_faces L K a b q p hLface hKface w hw)
      (by
        intro x hx
        obtain ⟨u, rfl⟩ := hKv.subset hx
        rw [hv, hw])
      (by
        intro y hy
        obtain ⟨u, rfl⟩ := hLv.subset hy
        rw [hw, hv])
  let e := (Homeomorph.setCongr hKs.symm).trans
    (H.trans (Homeomorph.setCongr hLs))
  have heval (x) : (e x : F) = f x := hH ⟨x, hKs.symm ▸ x.property⟩
  refine ⟨f, e, ⟨f, ⟨K, hK, hKs, hf⟩, heval⟩, ?_, heval⟩
  intro u
  exact (hfv (hKv.symm.subset (mem_range_self u))).trans (hv u)

end Geometry.SimplicialComplex
