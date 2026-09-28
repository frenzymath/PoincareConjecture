import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.FaceGerm
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.AffineInterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleGraphPosition



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem InTriangleGraphPosition.exists_whole_maximal_face_crossing
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X}
    (hposition : InTriangleGraphPosition Q S (g '' convexHull ℝ (s : Set E))
      (convexHull ℝ (A '' (s : Set E))))
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hgx : g x ∈ S)
    {O : Set V3} (hO : IsOpen O) (hxO : Q (g x) ∈ O) :
    ∃ B : OpenPartialHomeomorph V3 C3,
      Q (g x) ∈ B.source ∧ B.source ⊆ O ∩ Q.target ∧ B (Q (g x)) = 0 ∧
      LocallyPiecewiseAffineOn B B.source ∧
      LocallyPiecewiseAffineOn B.symm B.target ∧
      (∀ z ∈ B.source, Q.symm z ∈ S ↔ (B z).2 = 0) ∧
      ∀ z ∈ B.source, Q.symm z ∈ g '' K.space ↔ (B z).1.1 = 0 := by
  obtain ⟨W, hW, hxW, hwhole⟩ :=
    K.exists_original_maximal_face_image_germ hK hgc hgi hs hmax hx
  obtain ⟨G, hG, hGsub, hGcard, hphysical, hGi, hGb, hGfin, hcross⟩ := hposition
  have hxQ : g x ∈ Q.source := hmap (intrinsicInterior_subset hx)
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro a ha b hb hab
    exact hgi (K.convexHull_subset_space hs ha) (K.convexHull_subset_space hs hb)
      (Q.injOn (hmap ha) (hmap hb) ((hA ha).trans (hab.trans (hA hb).symm)))
  have hspan := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  have hcoord : Q (g x) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) := by
    rw [show Q (g x) = A x from hA (intrinsicInterior_subset hx)]
    have himage := A.toAffineMap.image_convexHull (s : Set E)
    change A x ∈ intrinsicInterior ℝ (convexHull ℝ (A.toAffineMap '' (s : Set E)))
    rw [← himage, A.toAffineMap.intrinsicInterior_image_of_injOn _ hspan]
    exact mem_image_of_mem A.toAffineMap hx
  have hxG : Q (g x) ∈ G.space := by
    have hp : g x ∈ Q.symm '' G.space :=
      hphysical.symm.subset ⟨hgx, x, intrinsicInterior_subset hx, rfl⟩
    obtain ⟨z, hz, heq⟩ := hp
    rw [← heq, Q.right_inv (hGsub hz).2]
    exact hz
  let V := O ∩ (Q.target ∩ Q.symm ⁻¹' W)
  have hV : IsOpen V := hO.inter (Q.symm.isOpen_inter_preimage hW)
  have hxV : Q (g x) ∈ V := by
    refine ⟨hxO, Q.map_source hxQ, ?_⟩
    simpa only [mem_preimage, Q.left_inv hxQ] using hxW
  obtain ⟨B, hxB, hBV, hBzero, hBPL, hBinv, hS, hT⟩ :=
    hcross (Q (g x)) ⟨hxG, hcoord⟩ V hV hxV
  have himage : Q '' (g '' convexHull ℝ (s : Set E)) =
      convexHull ℝ (A '' (s : Set E)) := by
    rw [image_image]
    calc
      (Q ∘ g) '' convexHull ℝ (s : Set E) = A '' convexHull ℝ (s : Set E) :=
        image_congr hA
      _ = convexHull ℝ (A '' (s : Set E)) := A.toAffineMap.image_convexHull _
  refine ⟨B, hxB, fun z hz => ⟨(hBV hz).1, (hBV hz).2.1⟩,
    hBzero, hBPL, hBinv, hS, ?_⟩
  intro z hz
  have hzQ := (hBV hz).2.1
  rw [hwhole (Q.symm z) (hBV hz).2.2]
  have heq : Q.symm z ∈ g '' convexHull ℝ (s : Set E) ↔
      z ∈ convexHull ℝ (A '' (s : Set E)) := by
    rw [← himage]
    constructor
    · intro hzface
      exact ⟨Q.symm z, hzface, Q.right_inv hzQ⟩
    · rintro ⟨y, ⟨u, hu, rfl⟩, heq⟩
      exact ⟨u, hu, (Q.left_inv (hmap hu)).symm.trans (congrArg Q.symm heq)⟩
  exact heq.trans (hT z hz)

end PoincareConjecture.M76
