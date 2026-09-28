import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.CommonEdgeOrbits
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexCycleConstancy










set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

local notation "L" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex

noncomputable local instance : DecidableEq K.vertices := Classical.decEq _

open Classical in
theorem surfaceVertexRotation_sameCycle_of_start_eq
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hlinks : ∀ v : K.vertices,
      (K.faceLink {v.val}).vertexAbstractComplex.edgeGraph.Preconnected)
    (number : K.vertices ↪ ℕ)
    (p : Triangle L → Fin 3 → K.vertices) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle L → ZMod 2)
    (hcancel : ∀ t u : Triangle L, t ≠ u → ∀ s : Edge L,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (hcofaces : ∀ e : Edge L, (triangleCofaces L e).card = 2)
    (d f : SurfaceDart L)
    (hstart : surfaceDartStart L p hp himage sigma d = surfaceDartStart L p hp himage sigma f) :
    (surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces).SameCycle d f := by
  let rho := surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces
  let v := surfaceDartStart L p hp himage sigma d
  let P (t : Triangle L) : Prop := ∃ a : SurfaceDart L,
    a.2.val = t ∧ surfaceDartStart L p hp himage sigma a = v ∧ rho.SameCycle d a
  have hstep (e : Edge L) (he : v ∈ e.val) (t u : Triangle L)
      (het : e.val ⊆ t.val) (heu : e.val ⊆ u.val) (ht : P t) : P u := by
    obtain ⟨a, ha, hav, hda⟩ := ht
    obtain ⟨b, hb, hbv⟩ := exists_surfaceDart_of_triangle_vertex L p hp himage sigma u v (heu he)
    refine ⟨b, hb, hbv, hda.trans ?_⟩
    apply surfaceVertexRotation_sameCycle_of_common_edge L number p hp himage hordered sigma hcancel
      hcofaces a b e v he
    · rwa [ha]
    · rwa [hb]
    · exact hav
    · exact hbv
  let a : Triangle K.toPreAbstractSimplicialComplex → Prop :=
    fun t => P ((K.vertexFaceEquiv 3).symm t)
  have hnext (w : (K.faceLink {v.val}).vertices)
      (u z : Triangle K.toPreAbstractSimplicialComplex)
      (hwu : insert w.val {v.val} ⊆ u.val)
      (hwz : insert w.val {v.val} ⊆ z.val) : a u = a z := by
    have hwface : insert w.val {v.val} ∈ K.faces := by
      simpa only [Finset.union_singleton] using w.property.2.2
    have hwcard : (insert w.val {v.val} : Finset E).card = 2 := by
      rw [Finset.card_insert_of_notMem
        (K.faceLink_vertices_subset {v.val} w.property).2, Finset.card_singleton]
    let e : Edge K.toPreAbstractSimplicialComplex := ⟨insert w.val {v.val}, hwface, hwcard⟩
    let e' : Edge L := (K.vertexFaceEquiv 2).symm e
    have hv : v ∈ e'.val := by
      apply (Finset.mem_map' (Function.Embedding.subtype _)).mp
      change v.val ∈ e'.val.map (Function.Embedding.subtype _)
      rw [show e'.val.map (Function.Embedding.subtype _) = e.val from K.vertexFaceEquiv_symm_map 2 e]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have heu : e'.val ⊆ ((K.vertexFaceEquiv 3).symm u).val := by
      apply Finset.map_subset_map.mp
      change e'.val.map (Function.Embedding.subtype _) ⊆
        ((K.vertexFaceEquiv 3).symm u).val.map (Function.Embedding.subtype _)
      dsimp only [e']
      rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
      exact hwu
    have hez : e'.val ⊆ ((K.vertexFaceEquiv 3).symm z).val := by
      apply Finset.map_subset_map.mp
      change e'.val.map (Function.Embedding.subtype _) ⊆
        ((K.vertexFaceEquiv 3).symm z).val.map (Function.Embedding.subtype _)
      dsimp only [e']
      rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
      exact hwz
    exact propext ⟨hstep e' hv _ _ heu hez, hstep e' hv _ _ hez heu⟩
  have hvd : v ∈ d.2.val.val := surfaceDart_start_mem_triangle L p hp himage sigma d
  have hvf : v ∈ f.2.val.val := by
    dsimp only [v]
    rw [hstart]
    exact surfaceDart_start_mem_triangle L p hp himage sigma f
  have hqd : {v.val} ⊆ (K.vertexFaceEquiv 3 d.2.val).val := by
    apply Finset.singleton_subset_iff.mpr
    exact Finset.mem_map.mpr ⟨v, hvd, rfl⟩
  have hqf : {v.val} ⊆ (K.vertexFaceEquiv 3 f.2.val).val := by
    apply Finset.singleton_subset_iff.mpr
    exact Finset.mem_map.mpr ⟨v, hvf, rfl⟩
  have h := K.triangle_coface_constancy_of_link a hpure (s := {v.val})
    (by simp) (by convert! hlinks v) hnext
    (K.vertexFaceEquiv 3 d.2.val) (K.vertexFaceEquiv 3 f.2.val) hqd hqf
  have hP : P d.2.val = P f.2.val := by
    simpa only [a, Equiv.symm_apply_apply] using h
  have hdP : P d.2.val := ⟨d, rfl, rfl, Equiv.Perm.SameCycle.rfl⟩
  obtain ⟨b, hb, hbv, hdb⟩ := hP ▸ hdP
  have hbf : b = f := surfaceDart_eq_of_triangle_start_eq L p hp himage sigma b f hb
    (hbv.trans hstart)
  exact hbf ▸ hdb

end Geometry.SimplicialComplex
