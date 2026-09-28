import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TransverseAffinePlaneCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicAffineGerms
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex






theorem exists_triangle_interior_crossing_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    {a b : Finset E} (ha : a ∈ K.faces) (hb : b ∈ L.faces)
    (ha3 : a.card = 3) (hb3 : b.card = 3)
    (hamax : ∀ c ∈ K.faces, a ⊆ c → c = a)
    (hbmax : ∀ c ∈ L.faces, b ⊆ c → c = b)
    (hjoin : affineSpan ℝ ((a : Set E) ∪ (b : Set E)) = ⊤)
    {p : E} (hpa : p ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
    (hpb : p ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set E)))
    {O : Set E} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ K.space ↔ (H x).2 = 0) ∧
      ∀ x ∈ H.source, x ∈ L.space ↔ (H x).1.1 = 0 := by
  obtain ⟨V, hV, hpV, hKV⟩ := K.exists_open_maximal_face_affine_germ hK ha hamax hpa
  obtain ⟨W, hW, hpW, hLW⟩ := L.exists_open_maximal_face_affine_germ hL hb hbmax hpb
  have hjoin' : affineSpan ℝ (a : Set E) ⊔ affineSpan ℝ (b : Set E) = ⊤ := by
    rw [← AffineSubspace.span_union]
    exact hjoin
  obtain ⟨F, hFzero, hFa, hFb⟩ :=
    (affineSpan ℝ (a : Set E)).exists_centered_crossing_coordinates
      (affineSpan ℝ (b : Set E)) hdim (K.finrank_faceDirection_of_card ha ha3)
      (L.finrank_faceDirection_of_card hb hb3) hjoin'
      (convexHull_subset_affineSpan (s := (a : Set E)) (intrinsicInterior_subset hpa))
      (convexHull_subset_affineSpan (s := (b : Set E)) (intrinsicInterior_subset hpb))
  let U := O ∩ (V ∩ W)
  have hU : IsOpen U := hO.inter (hV.inter hW)
  let H := F.symm.toHomeomorph.toOpenPartialHomeomorphOfImageEq U hU (F.symm '' U) rfl
  have hsource : H.source = U := rfl
  have hforward (x : E) : H x = F.symm x := rfl
  refine ⟨H, ⟨hpO, hpV, hpW⟩, fun _ hx => hx.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hforward, ← hFzero, F.symm_apply_apply]
  · exact locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap H.open_source
  · exact locallyPiecewiseAffineOn_affine F.toContinuousAffineMap H.open_target
  · intro x hx
    have hplane : x ∈ affineSpan ℝ (a : Set E) ↔ (F.symm x).2 = 0 := by
      simpa only [F.apply_symm_apply] using hFa (F.symm x)
    exact (hKV x ((hsource.subset hx).2.1)).trans hplane
  · intro x hx
    have hplane : x ∈ affineSpan ℝ (b : Set E) ↔ (F.symm x).1.1 = 0 := by
      simpa only [F.apply_symm_apply] using hFb (F.symm x)
    exact (hLW x ((hsource.subset hx).2.2)).trans hplane

end Geometry.SimplicialComplex
