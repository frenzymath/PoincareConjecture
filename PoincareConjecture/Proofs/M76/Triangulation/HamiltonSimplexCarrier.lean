import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCompactSimplexPresentation
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

section Carrier

variable {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]



def hamiltonModelCarrier {D : Set V} {C : Set X} (G : D ≃ₜ C) (B : Set V) : Set X :=
  (fun y : D => (G y : X)) '' (Subtype.val ⁻¹' B)



theorem hamiltonModelCarrier_mono {D : Set V} {C : Set X} (G : D ≃ₜ C)
    {B Q : Set V} (hBQ : B ⊆ Q) : hamiltonModelCarrier G B ⊆ hamiltonModelCarrier G Q :=
  image_mono (preimage_mono hBQ)



theorem isCompact_hamiltonModelCarrier {D : Set V} {C : Set X} (G : D ≃ₜ C)
    {B : Set V} (hB : IsCompact B) (hBD : B ⊆ D) : IsCompact (hamiltonModelCarrier G B) := by
  have hBsub : IsCompact ((Subtype.val : D → V) ⁻¹' B) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hB
      (by simpa only [Subtype.range_coe] using hBD)
  exact hBsub.image (continuous_subtype_val.comp G.continuous)



theorem disjoint_hamiltonModelCarrier {D : Set V} {C : Set X} (G : D ≃ₜ C)
    {B Q : Set V} (hBQ : Disjoint B Q) :
    Disjoint (hamiltonModelCarrier G B) (hamiltonModelCarrier G Q) := by
  apply disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
  have hzy : z = y := G.injective (Subtype.ext heq)
  subst z
  exact disjoint_left.mp hBQ hy hz

end Carrier

variable {X V E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]





theorem hamilton_face_coordinates
    {C : Set X} (K : SimplicialComplex ℝ V) (G : K.space ≃ₜ C)
    {s : Finset V} (hs : s ∈ K.faces) (c : OpenPartialHomeomorph X E)
    (a : V →ᴬ[ℝ] E)
    (hformula : ∀ y : K.space, (y : V) ∈ convexHull ℝ (s : Set V) →
      (G y : X) ∈ c.source ∧ c (G y) = a y)
    (hinj : InjOn a (convexHull ℝ (s : Set V))) :
    (s.image a).Nonempty ∧
    AffineIndependent ℝ ((↑) : s.image a → E) ∧
    convexHull ℝ (s.image a : Set E) ⊆ c.target ∧
    hamiltonModelCarrier G (convexHull ℝ (s : Set V)) =
      c.symm '' convexHull ℝ (s.image a : Set E) ∧
    hamiltonModelCarrier G (intrinsicFrontier ℝ (convexHull ℝ (s : Set V))) =
      c.symm '' intrinsicFrontier ℝ (convexHull ℝ (s.image a : Set E)) ∧
    hamiltonModelCarrier G (intrinsicInterior ℝ (convexHull ℝ (s : Set V))) =
      c.symm '' intrinsicInterior ℝ (convexHull ℝ (s.image a : Set E)) := by
  classical
  let D : Set V := convexHull ℝ (s : Set V)
  let T : Set E := convexHull ℝ (s.image a : Set E)
  have hD : IsCompact D := s.finite_toSet.isCompact_convexHull ℝ
  have hT : IsCompact T := (s.image a).finite_toSet.isCompact_convexHull ℝ
  have hDne : D.Nonempty := (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  have hDK : D ⊆ K.space := K.convexHull_subset_space hs
  have himage : a '' D = T := by
    change a.toAffineMap '' convexHull ℝ (s : Set V) =
      convexHull ℝ (s.image a : Set E)
    rw [Finset.coe_image]
    exact a.toAffineMap.image_convexHull (s : Set V)
  have hphysical {B : Set V} (hBD : B ⊆ D) :
      hamiltonModelCarrier G B = c.symm '' (a '' B) := by
    have hback (y : K.space) (hy : (y : V) ∈ B) : c.symm (a y) = (G y : X) := by
      obtain ⟨hyc, hya⟩ := hformula y (hBD hy)
      rw [← hya, c.left_inv hyc]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨a y, ⟨y, hy, rfl⟩, hback y hy⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      let y' : K.space := ⟨y, hDK (hBD hy)⟩
      exact ⟨y', hy, (hback y' hy).symm⟩
  have htarget : T ⊆ c.target := by
    rw [← himage]
    rintro _ ⟨y, hy, rfl⟩
    let y' : K.space := ⟨y, hDK hy⟩
    obtain ⟨hys, hyeq⟩ := hformula y' hy
    rw [← hyeq]
    exact c.map_source hys
  have hspan : InjOn a.toAffineMap (affineSpan ℝ D) :=
    a.toAffineMap.injOn_affineSpan_of_injOn_convex (convex_convexHull ℝ _) hDne hinj
  have hfront : intrinsicFrontier ℝ T = a '' intrinsicFrontier ℝ D := by
    rw [← himage]
    exact a.toAffineMap.intrinsicFrontier_image_of_injOn D hspan
  have hDclosure : intrinsicClosure ℝ D = D :=
    (hD.isClosed.preimage continuous_subtype_val).intrinsicClosure
  have hTclosure : intrinsicClosure ℝ T = T :=
    (hT.isClosed.preimage continuous_subtype_val).intrinsicClosure
  have hDdiff : D \ intrinsicFrontier ℝ D = intrinsicInterior ℝ D := by
    simpa only [hDclosure] using (intrinsicClosure_sdiff_intrinsicFrontier (𝕜 := ℝ) D)
  have hTdiff : T \ intrinsicFrontier ℝ T = intrinsicInterior ℝ T := by
    simpa only [hTclosure] using (intrinsicClosure_sdiff_intrinsicFrontier (𝕜 := ℝ) T)
  have hinterior : intrinsicInterior ℝ T = a '' intrinsicInterior ℝ D := by
    calc
      intrinsicInterior ℝ T = T \ intrinsicFrontier ℝ T := hTdiff.symm
      _ = a '' D \ a '' intrinsicFrontier ℝ D := by rw [himage, hfront]
      _ = a '' (D \ intrinsicFrontier ℝ D) :=
        (hinj.image_sdiff_subset (intrinsicFrontier_subset hD.isClosed)).symm
      _ = a '' intrinsicInterior ℝ D := congrArg (fun B => a '' B) hDdiff
  have hindep : AffineIndependent ℝ (fun y : s => a y) := by
    apply a.toAffineMap.affineIndependent_comp_of_injOn_convexHull (K.indep hs)
    change InjOn a (convexHull ℝ (range ((↑) : s → V)))
    rw [show range ((↑) : s → V) = (s : Set V) from Subtype.range_coe]
    exact hinj
  have hindepImage : AffineIndependent ℝ ((↑) : s.image a → E) := by
    have hrange : range (fun y : s => a y) = (s.image a : Set E) := by
      ext y
      simp
    have h := hindep.range
    change AffineIndependent ℝ ((↑) : ↥(range (fun y : s => a y)) → E) at h
    rw [hrange] at h
    exact h
  refine ⟨(K.nonempty_of_mem_faces hs).image a, hindepImage, htarget, ?_, ?_, ?_⟩
  · rw [hphysical (Subset.rfl : D ⊆ D), himage]
  · rw [hphysical (intrinsicFrontier_subset hD.isClosed), hfront]
  · rw [hphysical (intrinsicInterior_subset : intrinsicInterior ℝ D ⊆ D), hinterior]

end PoincareConjecture.M76
