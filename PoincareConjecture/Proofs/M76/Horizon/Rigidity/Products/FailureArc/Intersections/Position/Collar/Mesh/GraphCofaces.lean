import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PairMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.SourceRefinement
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartImageIntersection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.EdgeCofaces

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem finite_contacts_and_coface_charts_of_flattened_graph
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [DecidableEq D]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (K : SimplicialComplex ℝ D) {g : D → X} {p q : D}
    (hpq : ({p, q} : Finset D) ∈ K.faces)
    (Q : OpenPartialHomeomorph X E)
    (hQ : ∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans Q) ((e i).symm.trans Q).source)
    (hS : ∀ y ∈ Q.source, y ∈ S ↔ (Q y).2 = 0)
    (hp : g p ∉ S) (hq : g q ∉ S)
    (hcofaces : ∀ t ∈ K.faces, ({p, q} : Finset D) ⊆ t →
      MapsTo g (convexHull ℝ (t : Set D)) Q.source ∧
      ∃ A : D →ᴬ[ℝ] E, EqOn (Q ∘ g) A (convexHull ℝ (t : Set D))) :
    (S ∩ (g '' convexHull ℝ ({p, q} : Set D))).Finite ∧
      HasOriginalEdgeCofaceCharts e S K g {p, q} := by
  let L : E ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let B := Q.transHomeomorph L.toHomeomorph
  let A : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp
      L.symm.toContinuousAffineEquiv.toContinuousAffineMap
  have hB (i : ι) : (e i).symm.trans B ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (locallyPiecewiseAffineOn_affine
      L.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ).comp (hQ i)
    simp only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      preimage_univ, inter_univ] at h
    simp only [B,
      OpenPartialHomeomorph.transHomeomorph_eq_trans, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ, Function.comp_assoc]
    exact h.congr (fun _ _ => rfl)
  have hheight (y : X) : A (B y) = (Q y).2 := by
    change (L.symm (L (Q y))).2 = (Q y).2
    rw [L.symm_apply_apply]
  have hSB (z : V3) (hz : z ∈ B.target) : B.symm z ∈ S ↔ A z = 0 := by
    have hh := hS (B.symm z) (B.map_target hz)
    rwa [← hheight, B.right_inv hz] at hh
  have hcofacesB : ∀ t ∈ K.faces, ({p, q} : Finset D) ⊆ t →
      MapsTo g (convexHull ℝ (t : Set D)) B.source ∧
      ∃ M : D →ᴬ[ℝ] V3, EqOn (B ∘ g) M (convexHull ℝ (t : Set D)) := by
    intro t ht hpt
    obtain ⟨hmap, D, hD⟩ := hcofaces t ht hpt
    refine ⟨hmap, L.toContinuousAffineEquiv.toContinuousAffineMap.comp D, ?_⟩
    intro x hx
    exact congrArg L (hD hx)
  let C := S ∩ (g '' convexHull ℝ ({p, q} : Set D))
  by_cases hC : C.Nonempty
  swap
  · have hempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    refine ⟨by change C.Finite; rw [hempty]; exact finite_empty, ?_⟩
    intro y hy
    have : y ∈ C := by simpa only [Finset.coe_pair] using hy
    simp only [hempty, mem_empty_iff_false] at this
  obtain ⟨y, hyS, x, hx, hxy⟩ := hC
  obtain ⟨hmap, M, hM⟩ := hcofacesB {p, q} hpq (Subset.refl _)
  have hpH : p ∈ convexHull ℝ (({p, q} : Finset D) : Set D) := subset_convexHull ℝ _ (by simp)
  have hqH : q ∈ convexHull ℝ (({p, q} : Finset D) : Set D) := subset_convexHull ℝ _ (by simp)
  have hxH : x ∈ convexHull ℝ (({p, q} : Finset D) : Set D) := by simpa only [Finset.coe_pair] using hx
  have hpA : A (B (g p)) ≠ 0 := by
    rw [hheight]
    exact fun hh => hp ((hS _ (hmap hpH)).mpr hh)
  have hqA : A (B (g q)) ≠ 0 := by
    rw [hheight]
    exact fun hh => hq ((hS _ (hmap hqH)).mpr hh)
  have hxA : A (B (g x)) = 0 := by
    rw [hheight]
    exact (hS _ (hmap hxH)).mp (hxy.symm ▸ hyS)
  have hzero : (0 : ℝ) ∈ segment ℝ (A (B (g p))) (A (B (g q))) := by
    have hxseg : x ∈ segment ℝ p q := by simpa only [convexHull_pair] using hx
    have hm := mem_image_of_mem (A.toAffineMap.comp M.toAffineMap) hxseg
    rw [image_segment] at hm
    change A (M x) ∈ segment ℝ (A (M p)) (A (M q)) at hm
    rw [← hM hxH, ← hM hpH, ← hM hqH] at hm
    exact hxA ▸ hm
  rw [segment_eq_uIcc, mem_uIcc] at hzero
  rcases hzero with h | h
  · exact finite_contacts_and_coface_charts_of_affine_surface K hpq B hB A hSB
      (lt_of_le_of_ne h.1 hpA) (lt_of_le_of_ne h.2 hqA.symm) hcofacesB
  · apply finite_contacts_and_coface_charts_of_affine_surface K hpq B hB (-A)
      (fun z hz => (hSB z hz).trans (by simp)) ?_ ?_ hcofacesB
    · change -A (B (g p)) < 0
      exact neg_neg_of_pos (lt_of_le_of_ne h.2 hpA.symm)
    · change 0 < -A (B (g q))
      exact neg_pos.mpr (lt_of_le_of_ne h.1 hqA)

end PoincareConjecture.M76
