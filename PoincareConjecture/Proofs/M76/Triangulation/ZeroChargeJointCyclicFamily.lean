import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointOriginalCollar
import PoincareConjecture.Proofs.M76.Mathlib.ActualCommonCutBoxFamily
import PoincareConjecture.Proofs.M76.Mathlib.OriginalBoxProductCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.OriginalCyclicCollarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex











set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ}





theorem exists_original_collar_of_cyclic_boxes
    (P : Polygon V (n + 3)) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → V)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] V)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box r))
    (hFinj : ∀ i, InjOn (F i) (box r))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i)
    (hlateral : ∀ i (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F i ((u, if j then r else -r), z) =
        f (if j then finRotate (n + 3) i else i) ((u, 0), z))
    (hcontact : ∀ i, (F i '' box r) ∩ (F (finRotate (n + 3) i) '' box r) =
      f (finRotate (n + 3) i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r))
    (hdisjoint : ∀ i j, i ≠ j → finRotate (n + 3) i ≠ j → finRotate (n + 3) j ≠ i →
      Disjoint (F i '' box r) (F j '' box r))
    {S : Set V} (hS : IsCompact S) (A : V → ℝ) (c : ℝ) (hA : ContinuousOn A S)
    (hsection : S ∩ {x | A x = c} = P.boundary ℝ)
    (hheight : ∀ i x, x ∈ box r → A (F i x) = c + x.1.1)
    (hplane : ∀ i x, x ∈ box r → (F i x ∈ S ↔ x.2 = 0)) :
    ∃ tau : ℝ, tau ∈ Ioo 0 eta ∧
      ∃ G : (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
          Set (V × (ℝ × ℝ))) ≃ₜ (⋃ i, F i '' box r),
        G.IsFinitePL ∧
        (∀ p, A (G p) = c + (p : V × (ℝ × ℝ)).2.1) ∧
        (∀ p, (G p : V) ∈ S ↔ (p : V × (ℝ × ℝ)).2.2 = 0) ∧
        (∀ p : (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
          Set (V × (ℝ × ℝ))), (p : V × (ℝ × ℝ)).2 = 0 →
            (G p : V) = (p : V × (ℝ × ℝ)).1) ∧
        S ∩ {x | |A x - c| ≤ tau} ⊆ ⋃ i, F i '' box r := by
  obtain ⟨G, hG, hGinverse⟩ := P.exists_original_cyclic_product_collar t ht F
    (fun i => f i) hr hF hFinj hcore hlateral hcontact hdisjoint
  obtain ⟨hGheight, hGsurface, hGcore⟩ :=
    G.original_box_product_coordinates F hGinverse A c hheight hplane
  have hneighborhood := P.boundary_subset_interior_original_cyclic_boxes t ht F f
    hr hF hFinj hcore hlateral hcontact
  obtain ⟨tau, htau, hband⟩ := P.exists_surface_band_subset_original_neighborhood
    hS isOpen_interior hneighborhood A c hA hsection heta
  exact ⟨tau, htau, G, hG, hGheight, hGsurface, hGcore, hband.trans interior_subset⟩




theorem exists_joint_cylinder_of_cyclic_boxes
    (P : Polygon V (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P) (hdim : Module.finrank ℝ E = 2)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → V)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] V)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box r))
    (hFinj : ∀ i, InjOn (F i) (box r))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i)
    (hlateral : ∀ i (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F i ((u, if j then r else -r), z) =
        f (if j then finRotate (n + 3) i else i) ((u, 0), z))
    (hcontact : ∀ i, (F i '' box r) ∩ (F (finRotate (n + 3) i) '' box r) =
      f (finRotate (n + 3) i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r))
    (hdisjoint : ∀ i j, i ≠ j → finRotate (n + 3) i ≠ j → finRotate (n + 3) j ≠ i →
      Disjoint (F i '' box r) (F j '' box r))
    {S : Set V} (hS : IsCompact S) (A : V → ℝ) (c : ℝ) (hA : ContinuousOn A S)
    (hsection : S ∩ {x | A x = c} = P.boundary ℝ)
    (hheight : ∀ i x, x ∈ box r → A (F i x) = c + x.1.1)
    (hplane : ∀ i x, x ∈ box r → (F i x ∈ S ↔ x.2 = 0))
    (h : (E × ℝ) ≃ᴬ[ℝ] V) (hh : ∀ p, A (h p) = c + p.2)
    {d : Set E} (hd : IsCompact d) :
    ∃ epsilon : ℝ, epsilon ∈ Ioo 0 eta ∧
      ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
        d ⊆ interior K.space ∧
        (∀ v ∈ P.boundary ℝ, (h.symm v).1 ∈ interior K.space) ∧
        ∃ e : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) ≃ₜ
            (K.space ×ˢ Icc (-epsilon) epsilon),
          e.IsFinitePL ∧
          (∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2) ∧
          (∀ p : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)),
            (p : E × ℝ).2 = 0 → e p = p) ∧
          (∀ p, (e p : E × ℝ) ∈ h ⁻¹' S ↔
            (p : E × ℝ).1 ∈ (fun v : V => (h.symm v).1) '' P.boundary ℝ) ∧
          (h ⁻¹' S) ∩ {p | p.2 ∈ Icc (-epsilon) epsilon} ⊆
            K.space ×ˢ Icc (-epsilon) epsilon := by
  obtain ⟨tau, htau, C, hC, hCheight, hCsurface, hCcore, hband⟩ :=
    exists_original_collar_of_cyclic_boxes P t ht hr heta F f hF hFinj hcore
      hlateral hcontact hdisjoint hS A c hA hsection hheight hplane
  obtain ⟨epsilon, hepsilon, K, hK, hKconvex, hdK, hcoreK,
    e, he, heheight, hestart, hesection, heband⟩ :=
    exists_joint_cylinder_of_original_polygon_collar P hP hPinj hdim hr htau.1
      A h hh C hC hCheight hCsurface hCcore hband hd
  refine ⟨epsilon, ⟨hepsilon.1, ?_⟩, K, hK, hKconvex, hdK, hcoreK,
    e, he, heheight, hestart, hesection, heband⟩
  exact (hepsilon.2.trans_le (min_le_right _ _)).trans htau.2





theorem exists_joint_cylinder_of_actual_cut_boxes
    (P : Polygon V (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P) (hdim : Module.finrank ℝ E = 2)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (R : Fin (n + 3) → ℝ) (hR : ∀ i, 0 < R i)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → V)
    (H : Fin (n + 3) → OpenPartialHomeomorph V ((ℝ × ℝ) × ℝ))
    (σ k : Fin (n + 3) → Bool → ℝ)
    (hσ : ∀ i, σ i false < σ i true) (hk : ∀ i j, 0 < k i j)
    (hform : ∀ i, F i = (H i).symm ∘
      longitudinalPrismCoordinates (R i) (σ i false) (σ i true))
    (hsource : ∀ i, F i '' box (R i) ⊆ (H i).source)
    (hforward : ∀ i x, x ∈ box (R i) →
      H i (F i x) = longitudinalPrismCoordinates (R i) (σ i false) (σ i true) x)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box (R i)))
    (hFinj : ∀ i, InjOn (F i) (box (R i)))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-R i) (R i)) ×ˢ {0}) = P.cutArc t i)
    {S : Set V} (hS : IsCompact S) (A : V → ℝ) (c : ℝ) (hA : ContinuousOn A S)
    (hsection : S ∩ {x | A x = c} = P.boundary ℝ)
    (hheight : ∀ i x, x ∈ box (R i) → A (F i x) = c + x.1.1)
    (hplane : ∀ i x, x ∈ box (R i) → (F i x ∈ S ↔ x.2 = 0))
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] V)
    (hfzero : ∀ i, f i 0 = P.edgeCut t i)
    (hcutSource : ∀ i (j : Bool),
      f (if j then finRotate (n + 3) i else i) '' box (R i) ⊆ (H i).source)
    (hcutForward : ∀ i (j : Bool) x, x ∈ box (R i) →
      H i (f (if j then finRotate (n + 3) i else i) x) =
        ((x.1.1, σ i j + k i j * x.1.2), x.2))
    (h : (E × ℝ) ≃ᴬ[ℝ] V) (hh : ∀ p, A (h p) = c + p.2)
    {d : Set E} (hd : IsCompact d) {eta : ℝ} (heta : 0 < eta) :
    ∃ epsilon : ℝ, epsilon ∈ Ioo 0 eta ∧
      ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
        d ⊆ interior K.space ∧
        (∀ v ∈ P.boundary ℝ, (h.symm v).1 ∈ interior K.space) ∧
        ∃ e : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) ≃ₜ
            (K.space ×ˢ Icc (-epsilon) epsilon),
          e.IsFinitePL ∧
          (∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2) ∧
          (∀ p : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)),
            (p : E × ℝ).2 = 0 → e p = p) ∧
          (∀ p, (e p : E × ℝ) ∈ h ⁻¹' S ↔
            (p : E × ℝ).1 ∈ (fun v : V => (h.symm v).1) '' P.boundary ℝ) ∧
          (h ⁻¹' S) ∩ {p | p.2 ∈ Icc (-epsilon) epsilon} ⊆
            K.space ×ˢ Icc (-epsilon) epsilon := by
  obtain ⟨r, G, hr, _, hfamily, hcontact, hdisjoint⟩ :=
    P.exists_actual_common_cut_box_family hP hPinj t ht R hR F H σ k hσ hk
      hform hsource hforward hF hFinj hcore A c hheight hplane
      f hfzero hcutSource hcutForward heta
  simp only [forall_and] at hfamily
  rcases hfamily with ⟨_, _, hGPL, hGinj, _, _, _, hGheight, hGplane, hGcore, _, hGlateral⟩
  have htclosed (i : Fin (n + 3)) : t i ∈ Icc (0 : ℝ) 1 :=
    ⟨(ht i).1.le, (ht i).2.le⟩
  exact exists_joint_cylinder_of_cyclic_boxes P hP hPinj hdim t htclosed hr.1 heta G f
    hGPL hGinj hGcore hGlateral hcontact hdisjoint hS A c hA hsection
    hGheight hGplane h hh hd

end PoincareConjecture.M76.ZeroChargeJoint
