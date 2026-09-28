import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Planar.FrontierEdgeDeterminants
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.OrderedTriangleBoundary










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem exists_ordered_frontier_edge_chart
    (e : ι → OpenPartialHomeomorph X V3)
    (K J : SimplicialComplex ℝ E) (hJK : J ≤ K) (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g J.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ k, (e k).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)))
    (b : Module.Basis (Fin 3) ℝ V3)
    {s t u : Finset E} (hs : s ∈ J.faces) (ht : t ∈ J.faces) (hu : u ∈ J.faces)
    (hsc : s.card = 2) (htc : t.card = 3) (huc : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (p r : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hpt : Finset.univ.image p = t) (hru : Finset.univ.image r = u)
    (i j : Fin 3)
    (hsi : (Finset.univ.erase i).image p = s)
    (hsj : (Finset.univ.erase j).image r = s)
    (horder : p ∘ i.succAbove = r ∘ j.succAbove) :
    ∃ (C : OpenPartialHomeomorph X V3) (ell : V3 →ᴬ[ℝ] ℝ) (n : V3)
      (A D : E →ᴬ[ℝ] V3),
      (∀ k, (e k).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (convexHull ℝ (range p)) C.source ∧
      MapsTo g (convexHull ℝ (range r)) C.source ∧
      EqOn (C ∘ g) A (convexHull ℝ (range p)) ∧
      EqOn (C ∘ g) D (convexHull ℝ (range r)) ∧
      ell.contLinear n = 1 ∧
      (∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)) ∧
      ((-1 : ℝ) ^ i.val * b.det ![C (g (p 1)) - C (g (p 0)),
        C (g (p 2)) - C (g (p 0)), n]) *
      ((-1 : ℝ) ^ j.val * b.det ![C (g (r 1)) - C (g (r 0)),
        C (g (r 2)) - C (g (r 0)), n]) < 0 := by
  let perm : Fin 3 → Fin 3 := ![i.succAbove 0, i.succAbove 1, i]
  have hperm : Function.Injective perm := by
    fin_cases i <;> decide
  let p' : Fin 3 → E := p ∘ perm
  have hp' : AffineIndependent ℝ p' := hp.comp_embedding ⟨perm, hperm⟩
  have hp0s : p' 0 ∈ s := by
    rw [← hsi]
    exact Finset.mem_image.mpr ⟨i.succAbove 0,
      Finset.mem_erase.mpr ⟨Fin.succAbove_ne i 0, Finset.mem_univ _⟩, rfl⟩
  have hp't (k : Fin 3) : p' k ∈ t := by
    rw [← hpt]
    exact Finset.mem_image.mpr ⟨perm k, Finset.mem_univ _, rfl⟩
  have hsp (x : E) (hx : x ∈ s) : x = p' 0 ∨ x = p' 1 := by
    rw [← hsi] at hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hki := (Finset.mem_erase.mp hk).1
    obtain ⟨a, rfl⟩ := (Fin.exists_succAbove_eq hki)
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨C, ell, n, v, hC, hsource, haff, hn, hside, hvs, huv, hdet⟩ :=
    exists_frontier_edge_opposite_determinants e K J hJK g N hgi hfront hstars b
      hs ht hu hsc htc huc hst hsu htu p' hp' hp0s hp't hsp
  have hvj : v = r j := by
    have hvu : v ∈ u := huv.symm ▸ Finset.mem_insert_self _ _
    rw [← hru] at hvu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hvu
    by_cases hkj : k = j
    · exact congrArg r hkj
    · exact (hvs (hsj ▸ Finset.mem_image.mpr
        ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩, rfl⟩)).elim
  have htstar : t ∈ (J.closedStar (p' 0)).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hp0s)] using ht⟩
  have hustar : u ∈ (J.closedStar (p' 0)).faces :=
    ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hp0s)] using hu⟩
  have hpHull : convexHull ℝ (range p) ⊆ convexHull ℝ (t : Set E) := by
    apply convexHull_mono
    rintro _ ⟨k, rfl⟩
    rw [← hpt]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hrHull : convexHull ℝ (range r) ⊆ convexHull ℝ (u : Set E) := by
    apply convexHull_mono
    rintro _ ⟨k, rfl⟩
    rw [← hru]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  obtain ⟨A, hA⟩ := haff t htstar
  obtain ⟨D, hD⟩ := haff u hustar
  refine ⟨C, ell, n, A, D, hC,
    fun _ hx => hsource ((J.closedStar (p' 0)).convexHull_subset_space htstar (hpHull hx)),
    fun _ hx => hsource ((J.closedStar (p' 0)).convexHull_subset_space hustar (hrHull hx)),
    fun _ hx => hA (hpHull hx), fun _ hx => hD (hrHull hx), hn, hside, ?_⟩
  have h0 : p (i.succAbove 0) = r (j.succAbove 0) := congrFun horder 0
  have h1 : p (i.succAbove 1) = r (j.succAbove 1) := congrFun horder 1
  have hpdet := triangle_boundary_determinant b (C ∘ g ∘ p) n i
  have hrDet := triangle_boundary_determinant b (C ∘ g ∘ r) n j
  dsimp only [Function.comp_apply] at hpdet hrDet
  have hcombined := congrArg₂ (fun a b : ℝ => a * b) hpdet hrDet
  apply lt_of_eq_of_lt hcombined.symm
  change b.det ![C (g (p (i.succAbove 1))) - C (g (p (i.succAbove 0))),
    C (g (p i)) - C (g (p (i.succAbove 0))), n] *
    b.det ![C (g (r (j.succAbove 1))) - C (g (r (j.succAbove 0))),
    C (g (r j)) - C (g (r (j.succAbove 0))), n] < 0
  simpa [p', perm, hvj, h0, h1] using hdet

end PoincareConjecture.M76
