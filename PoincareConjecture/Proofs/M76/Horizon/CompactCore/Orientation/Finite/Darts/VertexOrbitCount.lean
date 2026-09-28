import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.WholeLinkOrbits

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

local notation "L" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex

noncomputable local instance : DecidableEq K.vertices := Classical.decEq _

open Classical in
theorem card_surfaceVertexRotation_orbits
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
    (hcofaces : ∀ e : Edge L, (triangleCofaces L e).card = 2) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
      (surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces))) =
      Fintype.card K.vertices := by
  let rho := surfaceTriangleRotation L p hp himage sigma * surfaceEdgePairing L hcofaces
  let start := surfaceDartStart L p hp himage sigma
  have hstep (d : SurfaceDart L) : start (rho d) = start d :=
    surfaceVertexRotation_preserves_start L number p hp himage hordered sigma hcancel hcofaces d
  have horbit {d f : SurfaceDart L} (h : rho.SameCycle d f) : start d = start f := by
    obtain ⟨n, _, _, hn⟩ := h.exists_pow_eq rho
    have hpow : ∀ n : ℕ, start ((rho ^ n) d) = start d := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih]
    rw [← hn, hpow]
  let q : Quotient (Equiv.Perm.SameCycle.setoid rho) → K.vertices :=
    Quotient.lift start (fun _ _ h => horbit h)
  have hqi : Function.Injective q := by
    intro x y h
    induction x using Quotient.inductionOn with
    | h d =>
      induction y using Quotient.inductionOn with
      | h f =>
        apply Quotient.sound
        exact K.surfaceVertexRotation_sameCycle_of_start_eq hpure
          (by intro v; convert! hlinks v) number p hp himage hordered sigma hcancel hcofaces d f h
  have hqs : Function.Surjective q := by
    intro v
    obtain ⟨t, ht, hvt, hcard⟩ := hpure {v.val} (K.mem_vertices.mp v.property)
    let T : Triangle K.toPreAbstractSimplicialComplex := ⟨t, ht, hcard⟩
    let t' : Triangle L := (K.vertexFaceEquiv 3).symm T
    have hv : v ∈ t'.val := by
      apply (Finset.mem_map' (Function.Embedding.subtype _)).mp
      change v.val ∈ t'.val.map (Function.Embedding.subtype _)
      rw [show t'.val.map (Function.Embedding.subtype _) = T.val from K.vertexFaceEquiv_symm_map 3 T]
      exact hvt (Finset.mem_singleton_self _)
    obtain ⟨d, _, hd⟩ := exists_surfaceDart_of_triangle_vertex L p hp himage sigma t' v hv
    exact ⟨Quotient.mk _ d, hd⟩
  exact (Nat.card_congr (Equiv.ofBijective q ⟨hqi, hqs⟩)).trans Nat.card_eq_fintype_card

end Geometry.SimplicialComplex
