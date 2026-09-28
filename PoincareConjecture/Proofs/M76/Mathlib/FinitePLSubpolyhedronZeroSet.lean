import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finitePL_subpolyhedron_zero_set
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (hJK : J.space ⊆ K.space) {r : ℝ} (hr : 0 < r) :
    ∃ f : E → ℝ, FinitePiecewiseAffineOn f K.space ∧
      ∀ x ∈ K.space, f x ∈ Icc 0 r ∧ (f x = 0 ↔ x ∈ J.space) := by
  classical
  obtain ⟨R, L, hR, hRK, hL⟩ := K.exists_subdivision_with_finite_full_polyhedra
    hK (fun _ : Unit => J) (fun _ => hJ) (fun _ => hJK)
  let N := L ()
  have hNR : N ≤ R := (hL ()).1
  have hNJ : N.space = J.space := (hL ()).2.1
  have hfull := (hL ()).2.2
  obtain ⟨f, hf, hfv⟩ := R.exists_affineOnFaces_eqOn_vertices
    (fun x => if x ∈ N.vertices then (0 : ℝ) else r)
  have hfN : N.AffineOnFaces f := fun s hs => hf s (hNR hs)
  have hzeroN : EqOn f (fun _ => 0) N.space := by
    apply hfN.eqOn_of_eqOn_vertices
      (N.affineOnFaces_affine (ContinuousAffineMap.const ℝ E (0 : ℝ)))
    intro v hv
    change f v = 0
    simpa only [if_pos hv] using hfv (hNR hv)
  refine ⟨f, ⟨R, hR, hRK.space_eq, hf⟩, fun x hx => ?_⟩
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hRK.space_eq.symm ▸ hx)
  obtain ⟨a, ha⟩ := hf s hs
  have hav (v : E) (hv : v ∈ s) : a v = if v ∈ N.vertices then 0 else r :=
    (ha (subset_convexHull ℝ _ hv)).symm.trans
      (hfv (R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)))
  have hbounds (v : E) (hv : v ∈ s) : a v ∈ Icc 0 r := by
    rw [hav v hv]
    split_ifs <;> constructor <;> linarith
  have hxbound : a x ∈ Icc (0 : ℝ) r :=
    convexHull_min (fun v hv => hbounds v hv)
      (Convex.affine_preimage a.toAffineMap (convex_Icc 0 r)) hxs
  refine ⟨ha hxs ▸ hxbound, ?_⟩
  constructor
  · intro hxzero
    have hz := s.mem_convexHull_zero_vertices a.toAffineMap
      (fun v hv => (hbounds v hv).1) hxs ((ha hxs).symm.trans hxzero)
    let t := s.filter (fun v => v ∈ N.vertices)
    have ht : (t : Set E) = (s : Set E) ∩ {v | a v = 0} := by
      ext v
      simp only [t, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hv, hvN⟩
        exact ⟨hv, by rw [hav v hv, if_pos hvN]⟩
      · rintro ⟨hv, hz⟩
        refine ⟨hv, ?_⟩
        by_contra hn
        rw [hav v hv, if_neg hn] at hz
        exact hr.ne' hz
    have hxt : x ∈ convexHull ℝ (t : Set E) := ht.symm ▸ hz
    have htne : t.Nonempty := by
      by_contra hn
      have hte := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [hte, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hxt
    have htR : t ∈ R.faces := R.down_closed hs (Finset.filter_subset _ _) htne
    have htN : t ∈ N.faces := hfull t htR (fun v hv => (Finset.mem_filter.mp hv).2)
    exact hNJ ▸ N.convexHull_subset_space htN hxt
  · intro hxJ
    exact hzeroN (hNJ.symm ▸ hxJ)

end Geometry.SimplicialComplex
