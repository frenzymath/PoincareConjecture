import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeSphereCollarsBodies
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeSphereCollarsEvent
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointCyclicFamily
import PoincareConjecture.Proofs.M76.Mathlib.InwardOrientedHeightCutBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHeightCutBoxes










set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}






theorem exists_original_sphere_collar
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hgeneric : InjOn A K.vertices) (c : ℝ)
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = c})
    (hsigns : ∀ x ∈ K.space, A x = c →
      x ∈ closure (K.space ∩ {y | A y < c}) ∧
        x ∈ closure (K.space ∩ {y | c < A y}))
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = c}))
    (hdplane : d ⊆ {x | A x = c}) {eta : ℝ} (heta : 0 < eta) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)) (r tau : ℝ) (T : Set E)
      (G : (Q.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
        Set (E × (ℝ × ℝ))) ≃ₜ T),
      Q.HasSimplicialEdges ∧ Function.Injective Q ∧
      Q.boundary ℝ = K.space ∩ {x | A x = c} ∧
      r ∈ Ioo 0 eta ∧ tau ∈ Ioo 0 eta ∧ G.IsFinitePL ∧
      (∀ p, A (G p) = c + (p : E × (ℝ × ℝ)).2.1) ∧
      (∀ p, (G p : E) ∈ K.space ↔ (p : E × (ℝ × ℝ)).2.2 = 0) ∧
      (∀ p : (Q.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
        Set (E × (ℝ × ℝ))), (p : E × (ℝ × ℝ)).2 = 0 →
          (G p : E) = (p : E × (ℝ × ℝ)).1) ∧
      K.space ∩ {x | |A x - c| ≤ tau} ⊆ T := by
  classical
  obtain ⟨N, Q, t, b, hQ, hQi, hQS, ht, hmarks, hbodyCuts⟩ :=
    exists_sphere_collar_body_family K hK hpure hcofaces hlinks hdim
      A hgeneric c P hP hPinj hsection
  have hbound (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    obtain ⟨u, _, huc, hsu⟩ := hpure s hs
    exact (Finset.card_le_card hsu).trans_eq huc
  have hcutHeight (i : Fin (N + 3)) : A (Q.edgeCut t i) = c := by
    apply (hQS.subset _).2
    exact mem_iUnion.mpr ⟨i, Q.edgeCut_mem_edgeSet t ⟨(ht i).1.le, (ht i).2.le⟩⟩
  obtain ⟨R0, f0, hR0, hf0, hf0disj⟩ :=
    K.exists_disjoint_affine_height_boxes_at_marks hK hbound hdim A hgeneric c
      (Q.edgeCut t) (Q.edgeCut_injective hQ hQi t ht) hcutHeight hmarks
      (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _) heta
  have hdQ : IsFinitePLBallPair (ℝ × ℝ) d (Q.boundary ℝ) := by rwa [hQS]
  obtain ⟨R, f, hR, _, hf, _⟩ :=
    Q.exists_inward_oriented_affine_height_cut_boxes hQ hQi t ht K.space A hA
      hdim c hQS hdQ hdplane (fun _ => univ) hR0.1 f0
      (fun i => ⟨(hf0 i).1, (hf0 i).2.1, (hf0 i).2.2.2.1, (hf0 i).2.2.2.2⟩)
      hf0disj heta
  have hfzero (i : Fin (N + 3)) : f i 0 = Q.edgeCut t i := (hf i).1
  have hfheight (i : Fin (N + 3)) (x : (ℝ × ℝ) × ℝ) :
      A (f i x) = c + x.1.1 := (hf i).2.2.2.2.1 x
  have hfsurface (i : Fin (N + 3)) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box R) :
      f i x ∈ K.space ↔ x.2 = 0 := (hf i).2.2.2.2.2.1 x hx
  have hfarc (i : Fin (N + 3)) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box R) :
      f i x ∈ Q.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2 :=
    ((hf i).2.2.2.2.2.2.1 x hx).1
  have hfinward (i : Fin (N + 3)) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ box R)
      (hxheight : x.1.1 = 0) : f i x ∈ d ↔ 0 ≤ x.2 :=
    (hf i).2.2.2.2.2.2.2 x hx hxheight
  choose s hs hsc htri using hmarks
  have hq (i : Fin (N + 3)) : Q (finRotate (N + 3) i) ∈ K.space ∩ {x | A x = c} :=
    hQS.subset (Q.vertex_mem_boundary _)
  have hevent (i : Fin (N + 3)) := exists_sphere_collar_event_box K hdim A c
    Q hQ hQi hQS t ht i (b i)
    (hsigns _ (hq i).1 (hq i).2).2 (hsigns _ (hq i).1 (hq i).2).1
    (fun j : Bool => s (if j then finRotate (N + 3) i else i))
    (fun j => hs _) (fun j => hsc _) (fun j => htri _) (hbodyCuts i)
    (fun j : Bool => f (if j then finRotate (N + 3) i else i))
    (fun j => hfzero _) hR.1 (fun j x hx => hfarc _ x hx)
    (fun j x => hfheight _ x) (fun j x hx => hfsurface _ x hx)
    hd hdplane (fun j x hx hxheight => hfinward _ x hx hxheight) heta
  choose radii H F k hradii hsmall hk hsource hform hFsource hF hFinj hball
    hheight hsurface hlateral hcutSource hcutForward hforward hcore using hevent
  let sigma : Fin (N + 3) → Bool → ℝ := fun _ j => if j then 1 else -1
  have hsigma (i : Fin (N + 3)) : sigma i false < sigma i true := by norm_num [sigma]
  obtain ⟨r, F', hr, _, hfamily, hcontact, hdisjoint⟩ :=
    Q.exists_actual_common_cut_box_family hQ hQi t ht radii (fun i => (hradii i).1)
      F H sigma k hsigma hk hform hFsource hforward hF hFinj hcore A c hheight
      hsurface f hfzero hcutSource hcutForward heta
  have hF' (i) : FinitePiecewiseAffineOn (F' i) (box r) := (hfamily i).2.2.1
  have hFinj' (i) : InjOn (F' i) (box r) := (hfamily i).2.2.2.1
  have hheight' (i) : ∀ x ∈ box r, A (F' i x) = c + x.1.1 :=
    (hfamily i).2.2.2.2.2.2.2.1
  have hsurface' (i) : ∀ x ∈ box r, F' i x ∈ K.space ↔ x.2 = 0 :=
    (hfamily i).2.2.2.2.2.2.2.2.1
  have hcore' (i) : F' i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = Q.cutArc t i :=
    (hfamily i).2.2.2.2.2.2.2.2.2.1
  have hlateral' (i) : ∀ (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F' i ((u, if j then r else -r), z) =
        f (if j then finRotate (N + 3) i else i) ((u, 0), z) :=
    (hfamily i).2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨tau, htau, G, hG, hGheight, hGsurface, hGcore, hband⟩ :=
    exists_original_collar_of_cyclic_boxes Q t (fun i => ⟨(ht i).1.le, (ht i).2.le⟩)
      hr.1 heta F' f hF' hFinj' hcore' hlateral' hcontact hdisjoint
      (K.isCompact_space_of_finite hK) A c A.continuous_of_finiteDimensional.continuousOn
      hQS.symm hheight' hsurface'
  exact ⟨N, Q, r, tau, ⋃ i, F' i '' box r, G, hQ, hQi, hQS,
    hr, htau, hG, hGheight, hGsurface, hGcore, hband⟩

end PoincareConjecture.M76.ZeroChargeJoint
