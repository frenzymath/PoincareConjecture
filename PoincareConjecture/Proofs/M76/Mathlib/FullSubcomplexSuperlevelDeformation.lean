import PoincareConjecture.Proofs.M76.Mathlib.InducedBarycentricCarrier
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph













set_option autoImplicit false

open Set StdSimplexCore unitInterval
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open scoped Classical in








theorem exists_full_subcomplex_superlevel_deformation_preserving_subcomplexes_mass
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) :
    ∃ w : E → ℝ, K.AffineOnFaces w ∧
      (∀ v ∈ K.vertices, w v = if v ∈ L.vertices then 1 else 0) ∧
      (∀ x ∈ L.space, w x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set E := {x | x ∈ K.space ∧ c ≤ w x}
        IsCompact N ∧ L.space ⊆ N ∧
          ∃ U : Set K.space, IsOpen U ∧
            (∀ x : K.space, (x : E) ∈ L.space → x ∈ U) ∧ Subtype.val '' U ⊆ N ∧
            ∃ H : C(I × N, E), (∀ z, H z ∈ N) ∧
              (∀ x : N, H (0, x) = (x : E)) ∧
              (∀ x : N, H (1, x) ∈ L.space) ∧
              (∀ (t : I) (x : N), (x : E) ∈ L.space → H (t, x) = (x : E)) ∧
              (∀ (B : SimplicialComplex ℝ E), B ≤ K →
                ∀ (t : I) (x : N), (x : E) ∈ B.space → H (t, x) ∈ B.space) ∧
              ∀ (t : I) (x : N), w (H (t, x)) =
                (1 - (t : ℝ)) * w x + (t : ℝ) := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let s := Finset.univ.filter (fun v : K.vertices => (v : E) ∈ L.vertices)
  let beta := barycentricMap ((↑) : K.vertices → E)
  let m : (K.vertices → ℝ) →L[ℝ] ℝ := ∑ i ∈ s, ContinuousLinearMap.proj i
  have hm (q : K.vertices → ℝ) : m q = ∑ i ∈ s, q i := by simp [m]
  obtain ⟨f, hf, hleft⟩ := K.exists_barycentric_leftInverse
  have hfK (x : E) (hx : x ∈ K.space) : f x ∈ A.barycentricSpace ∧ beta (f x) = x := by
    have hx' : x ∈ beta '' A.barycentricSpace := K.image_barycentricSpace.symm ▸ hx
    obtain ⟨q, hq, hqx⟩ := hx'
    have hfx : f x = q := by rw [← hqx]; exact hleft hq
    exact ⟨hfx.symm ▸ hq, by rw [hfx]; exact hqx⟩
  let D : Set (K.vertices → ℝ) := A.barycentricSpace ∩ barycentricFace s
  have hD : beta '' D = L.space :=
    (K.image_barycentric_vertexSubcomplex L.vertices).trans
      (congrArg SimplicialComplex.space (vertexSubcomplex_eq_of_full hLK hfull))
  have hfL (x : E) (hx : x ∈ L.space) : f x ∈ D := by
    obtain ⟨q, hq, hqx⟩ := hD.symm ▸ hx
    have hfx : f x = q := by rw [← hqx]; exact hleft hq.1
    exact hfx.symm ▸ hq
  let w : E → ℝ := m ∘ f
  have hw : K.AffineOnFaces w := hf.postcomp m.toContinuousAffineMap
  have hwL (x : E) (hx : x ∈ L.space) : w x = 1 :=
    (hm (f x)).trans (sum_eq_one_of_mem_barycentricFace (hfL x hx).2)
  have hfv (v : K.vertices) : f (v : E) = Pi.single v 1 := by
    have hsingle : Pi.single v (1 : ℝ) ∈ A.barycentricSpace := by
      apply A.barycentricFace_subset_barycentricSpace (K.vertexAbstractComplex.singleton_mem v)
      refine ⟨single_mem_stdSimplex ℝ v, ?_⟩
      intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [Ne.symm hi]
    simpa only [barycentricMap_single] using hleft hsingle
  refine ⟨w, hw, ?_, hwL, ?_⟩
  · intro v hv
    change m (f v) = _
    rw [hfv ⟨v, hv⟩, hm]
    simp [s, Pi.single_apply]
  · intro c hc hc1
    let N : Set E := {x | x ∈ K.space ∧ c ≤ w x}
    let B : Set (K.vertices → ℝ) :=
      {q | q ∈ A.barycentricSpace ∧ c ≤ ∑ i ∈ s, q i}
    obtain ⟨hB, _, _, _, _, _, T, hTB, hT0, hT1, hTfix, hTface, hTmass⟩ :=
      A.exists_barycentric_superlevel_deformation_preserving_faces_mass s hc hc1
    have hbetaN (q : B) : beta q ∈ N := by
      refine ⟨?_, ?_⟩
      · rw [← K.image_barycentricSpace]
        exact mem_image_of_mem beta q.property.1
      · change c ≤ m (f (beta q))
        rw [hleft q.property.1, hm]
        exact q.property.2
    have hfB (x : N) : f x ∈ B := by
      refine ⟨(hfK x x.property.1).1, ?_⟩
      rw [← hm]
      exact x.property.2
    have himage : beta '' B = N := by
      apply Subset.antisymm
      · rintro _ ⟨q, hq, rfl⟩
        exact hbetaN ⟨q, hq⟩
      · intro x hx
        exact ⟨f x, hfB ⟨x, hx⟩, (hfK x hx.1).2⟩
    have hN : IsCompact N := himage ▸ hB.image beta.continuous
    have hLN : L.space ⊆ N := fun x hx =>
      ⟨space_subset_of_le hLK hx, by rw [hwL x hx]; exact hc1.le⟩
    let U : Set K.space := {x | c < w x}
    have hwc : Continuous (fun x : K.space => w x) :=
      (hw.continuousOn hK).comp_continuous continuous_subtype_val (fun x => x.property)
    have hU : IsOpen U := isOpen_lt continuous_const hwc
    have hLU (x : K.space) (hx : (x : E) ∈ L.space) : x ∈ U := by
      change c < w x
      rw [hwL x hx]
      exact hc1
    have hUN : Subtype.val '' U ⊆ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.property, hx.le⟩
    let j : N → B := fun x => ⟨f x, hfB x⟩
    have hj : Continuous j :=
      ((hf.continuousOn hK).comp_continuous continuous_subtype_val
        (fun x : N => x.property.1)).subtype_mk _
    let H : C(I × N, E) :=
      ⟨fun z => beta (T (z.1, j z.2)), beta.continuous.comp
        (T.continuous.comp (continuous_fst.prodMk (hj.comp continuous_snd)))⟩
    refine ⟨hN, hLN, U, hU, hLU, hUN, H, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      exact hbetaN ⟨T (z.1, j z.2), hTB (z.1, j z.2)⟩
    · intro x
      change beta (T (0, j x)) = x
      rw [hT0]
      exact (hfK x x.property.1).2
    · intro x
      rw [← hD]
      exact mem_image_of_mem beta (hT1 (j x))
    · intro t x hx
      change beta (T (t, j x)) = x
      rw [hTfix t (j x) (hfL x hx)]
      exact (hfK x x.property.1).2
    · intro R hRK t x hx
      obtain ⟨r, hr, hxr⟩ := mem_space_iff.mp hx
      have hrK : r ∈ K.faces := hRK hr
      rw [K.faces_eq_vertexAbstractComplex_images] at hrK
      obtain ⟨u, hu, hur⟩ := hrK
      have hxu : (x : E) ∈ beta '' barycentricFace u := by
        change (x : E) ∈ barycentricMap ((↑) : K.vertices → E) '' barycentricFace u
        rw [image_barycentricFace, ← hur]
        exact hxr
      obtain ⟨q, hqu, hqx⟩ := hxu
      have hfq : f x = q := by
        rw [← hqx]
        exact hleft (A.barycentricFace_subset_barycentricSpace hu hqu)
      apply R.convexHull_subset_space hr
      rw [hur, ← image_barycentricFace ((↑) : K.vertices → E) u]
      refine ⟨T (t, j x), hTface t (j x) u ?_, rfl⟩
      change f x ∈ barycentricFace u
      rw [hfq]
      exact hqu
    · intro t x
      change m (f (beta (T (t, j x)))) = (1 - (t : ℝ)) * m (f x) + (t : ℝ)
      rw [hleft (hTB (t, j x)).1, hm, hTmass, hm]

open scoped Classical in



theorem exists_full_subcomplex_superlevel_deformation_preserving_subcomplexes
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) :
    ∃ w : E → ℝ, K.AffineOnFaces w ∧
      (∀ v ∈ K.vertices, w v = if v ∈ L.vertices then 1 else 0) ∧
      (∀ x ∈ L.space, w x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set E := {x | x ∈ K.space ∧ c ≤ w x}
        IsCompact N ∧ L.space ⊆ N ∧
          ∃ U : Set K.space, IsOpen U ∧
            (∀ x : K.space, (x : E) ∈ L.space → x ∈ U) ∧ Subtype.val '' U ⊆ N ∧
            ∃ H : C(I × N, E), (∀ z, H z ∈ N) ∧
              (∀ x : N, H (0, x) = (x : E)) ∧
              (∀ x : N, H (1, x) ∈ L.space) ∧
              (∀ (t : I) (x : N), (x : E) ∈ L.space → H (t, x) = (x : E)) ∧
              ∀ (B : SimplicialComplex ℝ E), B ≤ K →
                ∀ (t : I) (x : N), (x : E) ∈ B.space → H (t, x) ∈ B.space := by
  obtain ⟨w, hw, hwv, hwL, hlevel⟩ :=
    K.exists_full_subcomplex_superlevel_deformation_preserving_subcomplexes_mass L hK hLK hfull
  refine ⟨w, hw, hwv, hwL, ?_⟩
  intro c hc hc1
  obtain ⟨hN, hLN, U, hU, hLU, hUN, H, hHN, hH0, hH1, hfix, hpreserve, _⟩ :=
    hlevel c hc hc1
  exact ⟨hN, hLN, U, hU, hLU, hUN, H, hHN, hH0, hH1, hfix, hpreserve⟩

open scoped Classical in






theorem exists_full_subcomplex_superlevel_deformation
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) :
    ∃ w : E → ℝ, K.AffineOnFaces w ∧
      (∀ v ∈ K.vertices, w v = if v ∈ L.vertices then 1 else 0) ∧
      (∀ x ∈ L.space, w x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set E := {x | x ∈ K.space ∧ c ≤ w x}
        IsCompact N ∧ L.space ⊆ N ∧
          ∃ U : Set K.space, IsOpen U ∧
            (∀ x : K.space, (x : E) ∈ L.space → x ∈ U) ∧ Subtype.val '' U ⊆ N ∧
            ∃ H : C(I × N, E), (∀ z, H z ∈ N) ∧
              (∀ x : N, H (0, x) = (x : E)) ∧
              (∀ x : N, H (1, x) ∈ L.space) ∧
              ∀ (t : I) (x : N), (x : E) ∈ L.space → H (t, x) = (x : E) := by
  obtain ⟨w, hw, hwv, hwL, hlevel⟩ :=
    K.exists_full_subcomplex_superlevel_deformation_preserving_subcomplexes L hK hLK hfull
  refine ⟨w, hw, hwv, hwL, ?_⟩
  intro c hc hc1
  obtain ⟨hN, hLN, U, hU, hLU, hUN, H, hHN, hH0, hH1, hfix, _⟩ := hlevel c hc hc1
  exact ⟨hN, hLN, U, hU, hLU, hUN, H, hHN, hH0, hH1, hfix⟩

end Geometry.SimplicialComplex
