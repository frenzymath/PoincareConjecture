import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalEdgeCarriers
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.GeneralPosition.FiniteChartFaceControl
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.FiniteEdgeIndexing

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_controlled_original_skeleton
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [Nonempty X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E → X) (hfY : MapsTo f K.space Y)
    (B : K.vertices → OpenPartialHomeomorph X V3)
    (hcompat : ∀ v i, (e i).symm.trans (B v) ∈ piecewiseAffineGroupoid V3)
    (hsource : ∀ v : K.vertices, MapsTo f (K.closedStar v).space (B v).source)
    (hcoord : ∀ v : K.vertices, (K.closedStar v).AffineOnFaces (B v ∘ f)) :
    ∃ (a b : {s : K.faces // s.val.card = 2} → K.vertices)
      (v : {s : K.faces // s.val.card = 3} → K.vertices)
      (W : {s : K.faces // s.val.card = 3} → Set V3)
      (T : SimplicialComplex ℝ E) (G : C(I × T.space, X))
      (g : E → X) (p : K.vertices → C(I, X)),
      (∀ k, (a k : E) ≠ b k) ∧
      (∀ k, ({(a k : E), (b k : E)} : Finset E) = k.val.val) ∧
      (∀ s, (v s : E) ∈ s.val.val) ∧
      (∀ s, IsOpen (W s) ∧ Convex ℝ (W s) ∧ W s ⊆ (B (v s)).target ∧
        MapsTo (B (v s)).symm (W s) Y ∧
        MapsTo (B (v s) ∘ f) (convexHull ℝ (s.val.val : Set E)) (W s)) ∧
      T.faces.Finite ∧ T ≤ K ∧ T.space = ⋃ k, segment ℝ (a k : E) (b k : E) ∧
      (∀ v, p v 0 = f v) ∧ (∀ v t, p v t ∈ Y) ∧
      (∀ v : K.vertices, f v ∉ F → ∀ t, p v t = f v) ∧
      (∀ v (t : I), 0 < (t : ℝ) → p v t ∉ F) ∧
      (∀ z, G z ∈ Y) ∧
      (∀ k (t r : I) (hx : AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈ T.space),
        G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩) ∈ (B (a k)).source ∧
        B (a k) (G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩)) =
          AffineMap.lineMap (B (a k) (p (a k) t)) (B (a k) (p (b k) t)) (r : ℝ)) ∧
      (∀ s k, k.val.val ⊆ s.val.val → ∀ (t r : I)
        (hx : AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈ T.space),
        G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩) ∈ (B (v s)).source ∧
        B (v s) (G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩)) ∈ W s) ∧
      (∀ k (t : I) (ha : (a k : E) ∈ T.space) (hb : (b k : E) ∈ T.space),
        G (t, ⟨a k, ha⟩) = p (a k) t ∧ G (t, ⟨b k, hb⟩) = p (b k) t) ∧
      (∀ x : T.space, G (0, x) = f x) ∧
      (∀ x : T.space, G (1, x) = g x) ∧ PolyhedralPLInCharts e g T.space := by
  classical
  let : Finite K.faces := hK.to_subtype
  obtain ⟨a, b, hab, hpair, hinj⟩ := K.exists_actual_edge_endpoints
  have hedges (k : {s : K.faces // s.val.card = 2}) :
      {(a k : E), (b k : E)} ∈ K.faces := (hpair k).symm ▸ k.val.property
  choose w hw using fun s : {s : K.faces // s.val.card = 3} =>
    K.nonempty_of_mem_faces s.val.property
  have hwK (s : {s : K.faces // s.val.card = 3}) : w s ∈ K.vertices :=
    K.down_closed s.val.property (Finset.singleton_subset_iff.mpr (hw s))
      (Finset.singleton_nonempty _)
  let v : {s : K.faces // s.val.card = 3} → K.vertices := fun s => ⟨w s, hwK s⟩
  have hstar (s : {s : K.faces // s.val.card = 3}) :
      s.val.val ∈ (K.closedStar (v s)).faces := by
    refine ⟨s.val.property, ?_⟩
    change insert (w s) s.val.val ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (hw s)] using s.val.property
  obtain ⟨W, U, hW, hU, hinc⟩ :=
    OpenPartialHomeomorph.exists_finite_face_control K f hY hfY
      (fun s : {s : K.faces // s.val.card = 3} => s.val) (fun s => B (v s))
      (fun s _ hx => hsource (v s) (convexHull_subset_space (hstar s) hx))
      (fun s => hcoord (v s) _ (hstar s))
      (fun k => (a k : E)) (fun k => (b k : E)) hedges
  have hown (k : {s : K.faces // s.val.card = 2}) :
      MapsTo f (segment ℝ (a k : E) (b k : E)) (B (a k)).source := by
    have hs : {(a k : E), (b k : E)} ∈ (K.closedStar (a k)).faces := by
      refine ⟨hedges k, ?_⟩
      simpa only [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)] using hedges k
    intro x hx
    apply hsource (a k) (convexHull_subset_space hs ?_)
    simpa only [Finset.coe_pair, convexHull_pair] using hx
  let U' := fun k => U k ∩ (B (a k)).source
  obtain ⟨T, G, g, p, hT, hTK, hTS, hp0, hpY, hpfix, hpoff,
    hGY, hformula, hend, hG0, hG1, hgPL⟩ :=
    hN.exists_original_edge_carrier_homotopy hY hcut K f hfY a b hab hedges hinj
      (fun k => B (a k)) (fun k => hcompat (a k))
      (fun k => hsource (a k)) (fun k => hcoord (a k)) U'
      (fun k => (hU k).1.inter (B (a k)).open_source)
      (fun k => inter_subset_left.trans (hU k).2.1)
      (fun k _ hx => ⟨(hU k).2.2 hx, hown k hx⟩)
  refine ⟨a, b, v, W, T, G, g, p, hab, hpair, hw, hW, hT, hTK, hTS,
    hp0, hpY, hpfix, hpoff, hGY,
    fun k t r hx => ⟨(hformula k t r hx).1.2, (hformula k t r hx).2⟩,
    ?_, hend, hG0, hG1, hgPL⟩
  intro s k hks t r hx
  exact hinc k s ((hpair k).symm ▸ hks) (hformula k t r hx).1.1

end PoincareConjecture.M76
