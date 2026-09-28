import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroCrossing
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem finite_regular_level_of_affine_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2)
    {z : E → ℝ} (hz : K.AffineOnFaces z) {c : ℝ}
    (hreg : ∀ v ∈ K.vertices, z v ≠ c) : (K.space ∩ {x | z x = c}).Finite := by
  classical
  have hface (s : Finset E) (hs : s ∈ K.faces) :
      (convexHull ℝ (s : Set E) ∩ {x | z x = c}).Finite := by
    obtain ⟨A, hA⟩ := hz s hs
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    have hbound := hcard s hs
    rcases (show s.card = 1 ∨ s.card = 2 by omega) with hs1 | hs2
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hs1
      apply (finite_singleton p).subset
      simpa only [Finset.coe_singleton, convexHull_singleton] using
        (inter_subset_left : convexHull ℝ (({p} : Finset E) : Set E) ∩ {x | z x = c} ⊆ _)
    · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs2
      let B : E →ᵃ[ℝ] ℝ := A.toAffineMap - AffineMap.const ℝ E c
      have hB (x : E) (hx : x ∈ convexHull ℝ (({p, q} : Finset E) : Set E)) :
          B x = z x - c := by change A x - c = z x - c; rw [← hA hx]
      by_cases hdiff : B p ≠ B q
      · apply Set.Subsingleton.finite
        intro x hx y hy
        have hline {w : E} (hw : w ∈ convexHull ℝ (({p, q} : Finset E) : Set E)) :
            w ∈ affineSpan ℝ ({p, q} : Set E) :=
          convexHull_subset_affineSpan _ (by simpa only [Finset.coe_pair] using hw)
        have hx0 : B x = 0 := by rw [hB x hx.1, hx.2, sub_self]
        have hy0 : B y = 0 := by rw [hB y hy.1, hy.2, sub_self]
        exact (B.eq_zeroCrossing_of_mem_affineSpan hdiff (hline hx.1) hx0).trans
          (B.eq_zeroCrossing_of_mem_affineSpan hdiff (hline hy.1) hy0).symm
      · have heq := not_not.mp hdiff
        have hempty : convexHull ℝ (({p, q} : Finset E) : Set E) ∩ {x | z x = c} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hxseg : x ∈ segment ℝ p q := by simpa only [Finset.coe_pair, convexHull_pair] using hx.1
          have himage := mem_image_of_mem B hxseg
          rw [image_segment, ← heq, segment_same, mem_singleton_iff] at himage
          have hpH : p ∈ convexHull ℝ (({p, q} : Finset E) : Set E) :=
            subset_convexHull ℝ _ (by simp)
          have hpV : p ∈ K.vertices := K.down_closed hs (by simp) (Finset.singleton_nonempty p)
          have hzpc : z p = c := by rw [hB x hx.1, hB p hpH, hx.2] at himage; linarith
          exact hreg p hpV hzpc
        rw [hempty]
        exact finite_empty
  apply (hK.biUnion hface).subset
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx.1
  exact mem_iUnion₂.mpr ⟨s, hs, hxs, hx.2⟩

theorem exists_regular_finitePL_level_in_line_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {S : Set E} {z : E → ℝ} (hz : FinitePiecewiseAffineOn z S)
    (lines : Finset (AffineSubspace ℝ E))
    (hdim : ∀ A ∈ lines, Module.finrank ℝ A.direction ≤ 1)
    (hcover : ∀ x ∈ S, ∃ A ∈ lines, x ∈ A)
    {a b : ℝ} (hab : a < b) :
    ∃ (c : ℝ) (K : SimplicialComplex ℝ E),
      c ∈ Ioo a b ∧ K.faces.Finite ∧ K.space = S ∧
      (∀ s ∈ K.faces, s.card ≤ 2) ∧ K.AffineOnFaces z ∧
      (∀ v ∈ K.vertices, z v ≠ c) ∧ (S ∩ {x | z x = c}).Finite ∧
      ∀ x ∈ S ∩ {x | z x = c}, ∃ s ∈ K.faces, s.card = 2 ∧
        x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨K, hK, hKs, hfaces⟩ := hz
  have hcard : ∀ s ∈ K.faces, s.card ≤ 2 := fun _ hs =>
    K.face_card_le_of_finite_affine_cover lines hdim (fun x hx => hcover x (hKs.subset hx)) hs
  obtain ⟨c, hc, hcnot⟩ := (Ioo_infinite hab).exists_notMem_finite
    ((K.finite_vertices_of_finite_faces hK).image z)
  have hreg (v : E) (hv : v ∈ K.vertices) : z v ≠ c :=
    fun heq => hcnot ⟨v, hv, heq⟩
  have hfinite := finite_regular_level_of_affine_graph K hK hcard hfaces hreg
  refine ⟨c, K, hc, hK, hKs, hcard, hfaces, hreg, hKs ▸ hfinite, ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK (hKs.symm.subset hx.1)
  refine ⟨s, hs, ?_, hxs⟩
  have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hbound := hcard s hs
  by_contra hn
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
  have hxv : x = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff]
      using intrinsicInterior_subset hxs
  exact hreg v hs (hxv ▸ hx.2)

end PoincareConjecture.M76
