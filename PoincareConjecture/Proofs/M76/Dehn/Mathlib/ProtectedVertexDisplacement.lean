import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_protected_vertex_height (J Q : SimplicialComplex ℝ E)
    (hQJ : Q ≤ J) {v : E} (hv : v ∈ J.vertices) (hvQ : v ∉ Q.vertices) :
    ∃ f : E → ℝ, J.AffineOnFaces f ∧ f v = 1 ∧
      (∀ w ∈ J.vertices, w ≠ v → f w = 0) ∧
      MapsTo f J.space (Icc 0 1) ∧ EqOn f (fun _ => 0) Q.space := by
  classical
  obtain ⟨f, hf, hfv⟩ := J.exists_affineOnFaces_eqOn_vertices
    (fun x => if x = v then (1 : ℝ) else 0)
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · simpa using hfv hv
  · intro w hw hwv
    simpa only [if_neg hwv] using hfv hw
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := hf s hs
    rw [ha hxs]
    apply convexHull_min ?_ ((convex_Icc (0 : ℝ) 1).affine_preimage a.toAffineMap) hxs
    intro w hw
    have hwJ : w ∈ J.vertices :=
      J.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
    change a w ∈ Icc (0 : ℝ) 1
    rw [← ha (subset_convexHull ℝ _ hw), hfv hwJ]
    change (if w = v then (1 : ℝ) else 0) ∈ Icc 0 1
    split_ifs <;> norm_num
  · have hfQ : Q.AffineOnFaces f := fun s hs => hf s (hQJ hs)
    apply hfQ.eqOn_of_eqOn_vertices
      (Q.affineOnFaces_affine (ContinuousAffineMap.const ℝ E (0 : ℝ)))
    intro w hw
    have hwv : w ≠ v := fun h => hvQ (h ▸ hw)
    change f w = 0
    simpa only [if_neg hwv] using hfv (hQJ hw)





theorem exists_protected_vertex_displacement (J Q : SimplicialComplex ℝ E)
    (hQJ : Q ≤ J) {v : E} (hv : v ∈ J.vertices) (hvQ : v ∉ Q.vertices) (u : E) :
    ∃ f : E → E, J.AffineOnFaces f ∧ f v = u ∧
      (∀ w ∈ J.vertices, w ≠ v → f w = 0) ∧
      (∀ x ∈ J.space, ‖f x‖ ≤ ‖u‖) ∧ EqOn f (fun _ => 0) Q.space := by
  obtain ⟨g, hg, hgv, hgw, hgb, hgQ⟩ := J.exists_protected_vertex_height Q hQJ hv hvQ
  let f : E → E := fun x => g x • u
  have hf : J.AffineOnFaces f :=
    hg.postcomp ((ContinuousLinearMap.id ℝ ℝ).smulRight u).toContinuousAffineMap
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · change g v • u = u
    rw [hgv, one_smul]
  · intro w hw hwv
    change g w • u = 0
    rw [hgw w hw hwv, zero_smul]
  · intro x hx
    change ‖g x • u‖ ≤ ‖u‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgb hx).1]
    nlinarith [(hgb hx).2, norm_nonneg u]
  · intro x hx
    change g x • u = 0
    rw [hgQ hx, zero_smul]

end Geometry.SimplicialComplex
