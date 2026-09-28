import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_edge_subcomplex_coordinate (K : SimplicialComplex ℝ E)
    {a b : E} (hab : a ≠ b) (hedge : {a, b} ∈ K.faces) :
    ∃ (J : SimplicialComplex ℝ E) (l : E →ᴬ[ℝ] ℝ),
      J.faces.Finite ∧ J ≤ K ∧ J.space = segment ℝ a b ∧
      l a = 0 ∧ l b = 1 ∧
      (∀ t : ℝ, l (AffineMap.lineMap a b t) = t) ∧
      MapsTo l J.space (Icc 0 1) ∧
      ∀ x ∈ J.space, AffineMap.lineMap a b (l x) = x := by
  classical
  let A : Finset K.faces := {⟨{a, b}, hedge⟩}
  let J := K.finiteFaceSpan A
  have hface : {a, b} ∈ J.faces := by
    apply (K.finiteFaceSpan_faces A _).mpr
    exact ⟨by simp, ⟨{a, b}, hedge⟩, Finset.mem_singleton_self _, Finset.Subset.refl _⟩
  have hspace : J.space = segment ℝ a b := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      obtain ⟨_, t, ht, hst⟩ := (K.finiteFaceSpan_faces A s).mp hs
      have ht' : t = ⟨{a, b}, hedge⟩ := Finset.mem_singleton.mp ht
      subst t
      have hx' := convexHull_mono (show (s : Set E) ⊆ ({a, b} : Finset E) from hst) hxs
      simpa only [Finset.coe_pair, convexHull_pair] using hx'
    · intro hx
      apply J.convexHull_subset_space hface
      simpa only [Finset.coe_pair, convexHull_pair] using hx
  obtain ⟨l, hl⟩ := (K.indep hedge).exists_continuousAffineMap_eqOn
    (fun x : E => if x = a then (0 : ℝ) else 1)
  have hla : l a = 0 := by simpa using hl (show a ∈ ({a, b} : Finset E) by simp)
  have hlb : l b = 1 := by simpa [hab.symm] using hl (show b ∈ ({a, b} : Finset E) by simp)
  have hline (t : ℝ) : l (AffineMap.lineMap a b t) = t := by
    change l.toAffineMap (AffineMap.lineMap a b t) = t
    rw [AffineMap.apply_lineMap]
    change AffineMap.lineMap (l a) (l b) t = t
    rw [hla, hlb]
    simp [AffineMap.lineMap_apply]
  have hparam (x : E) (hx : x ∈ J.space) :
      ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap a b t = x := by
    rw [hspace, segment_eq_image_lineMap] at hx
    exact hx
  refine ⟨J, l, K.finiteFaceSpan_finite A, K.finiteFaceSpan_le A,
    hspace, hla, hlb, hline, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hparam x hx
    simpa only [hline] using ht
  · intro x hx
    obtain ⟨t, _, rfl⟩ := hparam x hx
    rw [hline]

theorem exists_edge_homotopy_transport
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : ι → OpenPartialHomeomorph X V}
    (K : SimplicialComplex ℝ E) {a b : E}
    (hab : a ≠ b) (hedge : {a, b} ∈ K.faces)
    (H : C(I × I, X)) {q : ℝ → X}
    (hq : PolyhedralPLInCharts e q (Icc 0 1))
    (hH1 : ∀ s : I, H (1, s) = q s) :
    ∃ (J : SimplicialComplex ℝ E) (l : E →ᴬ[ℝ] ℝ) (G : C(I × J.space, X)),
      J.faces.Finite ∧ J ≤ K ∧ J.space = segment ℝ a b ∧
      l a = 0 ∧ l b = 1 ∧
      (∀ t : ℝ, l (AffineMap.lineMap a b t) = t) ∧
      MapsTo l J.space (Icc 0 1) ∧
      (∀ x ∈ J.space, AffineMap.lineMap a b (l x) = x) ∧
      (∀ (t : I) (x : J.space) (s : I),
        (x : E) = AffineMap.lineMap a b (s : ℝ) → G (t, x) = H (t, s)) ∧
      (∀ f : E → X, (∀ s : I, H (0, s) = f (AffineMap.lineMap a b (s : ℝ))) →
        ∀ x : J.space, G (0, x) = f x) ∧
      (∀ x : J.space, G (1, x) = q (l x)) ∧
      PolyhedralPLInCharts e (q ∘ l) J.space := by
  obtain ⟨J, l, hJ, hJK, hspace, hla, hlb, hline, hmap, hinv⟩ :=
    K.exists_edge_subcomplex_coordinate hab hedge
  let p : C(I × J.space, I × I) :=
    ⟨fun z => (z.1, ⟨l z.2, hmap z.2.property⟩),
      continuous_fst.prodMk
        ((l.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)⟩
  let G := H.comp p
  refine ⟨J, l, G, hJ, hJK, hspace, hla, hlb, hline, hmap, hinv, ?_, ?_, ?_, ?_⟩
  · intro t x s hxs
    have heq : (⟨l x, hmap x.property⟩ : I) = s := by
      apply Subtype.ext
      change l x = (s : ℝ)
      rw [hxs, hline]
    change H (t, ⟨l x, hmap x.property⟩) = H (t, s)
    rw [heq]
  · intro f hf x
    change H (0, ⟨l x, hmap x.property⟩) = f x
    rw [hf, hinv x x.property]
  · intro x
    exact hH1 ⟨l x, hmap x.property⟩
  · exact hq.comp_finitePiecewiseAffineOn J hJ
      ⟨J, hJ, rfl, J.affineOnFaces_affine l⟩ hmap

end Geometry.SimplicialComplex
