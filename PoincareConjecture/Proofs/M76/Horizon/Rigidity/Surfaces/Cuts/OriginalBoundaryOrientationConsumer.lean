import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PlanarBoundaryOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalRefinementCoherentSigns
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeReversal
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskConnectedLink
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleAdjacency

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem convex_puncture_isConnected {S : Set E} (hS : Convex ℝ S)
    (hne : (interior S).Nonempty) (hdim : 1 < Module.finrank ℝ E) (p : E) :
    IsConnected (S \ {p}) := by
  have hc : IsConnected (interior S \ {p}) := by
    simpa using (AffineSubspace.isPathConnected_sdiff_iUnion
      (fun _ : Unit ↦ affineSpan ℝ ({p} : Set E))
      (fun _ ↦ by
        rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
        exact hdim) isOpen_interior hS.interior hne).isConnected
  apply hc.subset_closure (show interior S \ {p} ⊆ S \ {p} from
    fun _ hx ↦ ⟨interior_subset hx.1, hx.2⟩)
  intro x hx
  have hxcl : x ∈ closure (interior S) := by
    rw [hS.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure hx.1
  apply mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨y, hy, hyint⟩ := mem_closure_iff.mp hxcl
    (U \ {p}) (hU.sdiff isClosed_singleton) ⟨hxU, hx.2⟩
  exact ⟨y, hy.1, hyint, hy.2⟩

theorem convex_carrier_vertex_link_isConnected [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (hdim : 1 < Module.finrank ℝ E) {p : E} (hp : p ∈ K.vertices) :
    IsConnected (K.faceLink {p}).space := by
  have hpK : p ∈ K.space := K.vertices_subset_space hp
  have hstar : (K.closedFaceStar {p}).space ∈ 𝓝[K.space] p := by
    rw [← map_nhds_subtype_val (⟨p, hpK⟩ : K.space)]
    apply K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hp
    simp
  obtain ⟨U, hU, hpU, hUstar⟩ := mem_nhdsWithin.mp hstar
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  let S := Metric.ball p ε ∩ K.space
  have hSint : (interior S).Nonempty := by
    have hpcl : p ∈ closure (interior K.space) := by
      rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne]
      exact subset_closure hpK
    obtain ⟨x, hxball, hxint⟩ := mem_closure_iff.mp hpcl (Metric.ball p ε)
      Metric.isOpen_ball (Metric.mem_ball_self hε)
    refine ⟨x, ?_⟩
    simpa only [S, interior_inter, Metric.isOpen_ball.interior_eq, mem_inter_iff] using
      (And.intro hxball hxint)
  have hB : IsConnected (S \ {p}) :=
    convex_puncture_isConnected ((convex_ball p ε).inter hcv) hSint hdim p
  have hBstar : S \ {p} ⊆ (K.closedFaceStar {p}).space \ {p} := by
    intro x hx
    exact ⟨hUstar ⟨hball hx.1.1, hx.1.2⟩, hx.2⟩
  have hnear : insert p (S \ {p}) ∈ 𝓝[K.space] p := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hε),
      self_mem_nhdsWithin] with x hxball hxK
    by_cases hxp : x = p
    · exact Or.inl hxp
    · exact Or.inr ⟨⟨hxball, hxK⟩, hxp⟩
  rw [K.faceLink_singleton_eq_link]
  exact K.isConnected_link_of_punctured_neighborhood hK hB hBstar hnear

theorem convex_planar_triangleGraph_connected [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (hdim : Module.finrank ℝ E = 2) :
    (PreAbstractSimplicialComplex.ModTwoCochains.triangleGraph
      K.toPreAbstractSimplicialComplex).Connected := by
  apply K.triangleGraph_connected_of_isConnected hK
  · intro s hs
    obtain ⟨t, ht, hst, htc⟩ := K.exists_full_coface_of_convex_space hK hcv hne hs
    exact ⟨t, ht, hst, by omega⟩
  · exact hcv.isConnected (hne.mono interior_subset)
  · intro p hp
    exact convex_carrier_vertex_link_isConnected K hK hcv hne (by omega) hp

theorem planar_boundary_cycle_uniform_direction_at
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hcv : Convex ℝ K.space)
    (z : ℝ × ℝ) (hz : z ∈ interior K.space)
    (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3)) (hPi : Function.Injective P)
    (hedge : ∀ i, {P i, P (finRotate (n + 3) i)} ∈
      (K.frontierSubcomplex K.space).faces) :
    (∀ i, 0 < planarCross (P i - z) (P (finRotate (n + 3) i) - z)) ∨
      (∀ i, planarCross (P i - z) (P (finRotate (n + 3) i) - z) < 0) := by
  classical
  let e : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) := ContinuousAffineEquiv.constVAdd ℝ _ (-z)
  let hf := K.affineOnFaces_affine e.toContinuousAffineMap
  let J := hf.embeddedImage e.injective.injOn
  have hJs : J.space = e '' K.space := hf.embeddedImage_space e.injective.injOn
  have he (x : ℝ × ℝ) : e x = x - z := by
    change -z + x = x - z
    abel
  have hJcv : Convex ℝ J.space := by
    rw [hJs]
    exact hcv.affine_image e.toAffineEquiv.toAffineMap
  have hzero : (0 : ℝ × ℝ) ∈ interior J.space := by
    rw [hJs]
    change (0 : ℝ × ℝ) ∈ interior (e.toHomeomorph '' K.space)
    rw [← e.toHomeomorph.image_interior]
    exact ⟨z, hz, by change e z = 0; rw [he, sub_self]⟩
  let Q : Polygon (ℝ × ℝ) (n + 3) := ⟨e ∘ P⟩
  have hQi : Function.Injective Q := e.injective.comp hPi
  have hedgeQ (i : Fin (n + 3)) :
      {Q i, Q (finRotate (n + 3) i)} ∈ (J.frontierSubcomplex J.space).faces := by
    refine ⟨?_, ?_⟩
    · change {e (P i), e (P (finRotate (n + 3) i))} ∈ J.faces
      rw [hf.embeddedImage_faces e.injective.injOn]
      exact ⟨{P i, P (finRotate (n + 3) i)}, (hedge i).1, by simp⟩
    · intro x hx
      have hx' : x ∈ convexHull ℝ (e '' ({P i, P (finRotate (n + 3) i)} : Set _)) := by
        simpa only [image_pair, Finset.coe_pair, Q,
          Function.comp_apply] using hx
      change x ∈ convexHull ℝ (e.toAffineEquiv.toAffineMap ''
        ({P i, P (finRotate (n + 3) i)} : Set _)) at hx'
      rw [← e.toAffineEquiv.toAffineMap.image_convexHull] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      rw [hJs]
      change e y ∈ frontier (e.toHomeomorph '' K.space)
      rw [← e.toHomeomorph.image_frontier]
      exact mem_image_of_mem e ((hedge i).2 (by simpa using hy))
  simpa only [Q, Function.comp_apply, he] using
    planar_boundary_cycle_uniform_direction J hJcv hzero n Q hQi hedgeQ

theorem exists_oriented_planar_boundary_cycle_at
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (z : ℝ × ℝ) (hz : z ∈ interior K.space) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3))
      (edge : Fin (n + 3) ≃
        {s : Finset (ℝ × ℝ) // s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2})
      (coface : Fin (n + 3) → Finset (ℝ × ℝ)) (apex : Fin (n + 3) → ℝ × ℝ),
      Function.Injective P ∧ P.boundary ℝ = frontier K.space ∧
      Equiv.Perm.IsCycle (finRotate (n + 3)) ∧
      (∀ i, (edge i).val = {P i, P (finRotate (n + 3) i)}) ∧
      (∀ i, coface i ∈ K.faces ∧ (edge i).val ⊆ coface i ∧ (coface i).card = 3) ∧
      (∀ i t, t ∈ K.faces → (edge i).val ⊆ t → t.card = 3 → t = coface i) ∧
      (∀ i, apex i ∈ coface i ∧ apex i ≠ P i ∧ apex i ≠ P (finRotate (n + 3) i)) ∧
      ((∀ i, 0 < planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i)) ∨
        (∀ i, planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i) < 0)) := by
  classical
  obtain ⟨n, P, edge, coface, hPi, hPb, hcycle, hedge, hcoface, huniq⟩ :=
    exists_planar_boundary_dart_cycle K hK hcv ⟨z, hz⟩
  have hapex (i : Fin (n + 3)) :
      ∃ x ∈ coface i, x ≠ P i ∧ x ≠ P (finRotate (n + 3) i) := by
    obtain ⟨x, hx, hxt⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨(hcoface i).2.1, by rw [(edge i).property.2, (hcoface i).2.2]⟩
    refine ⟨x, hxt ▸ Finset.mem_insert_self _ _, ?_⟩
    simpa only [hedge i, Finset.mem_insert, Finset.mem_singleton, not_or] using hx
  choose apex hapex using hapex
  have hedges (i : Fin (n + 3)) :
      {P i, P (finRotate (n + 3) i)} ∈ (K.frontierSubcomplex K.space).faces :=
    hedge i ▸ (edge i).property.1
  have hcross (a b : ℝ × ℝ) :
      planarCross (b - a) (z - a) = planarCross (a - z) (b - z) := by
    dsimp [planarCross]
    ring
  have hprod (i : Fin (n + 3))
      (hd : planarCross (P i - z) (P (finRotate (n + 3) i) - z) ≠ 0) :
      0 < planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i) *
        planarCross (P i - z) (P (finRotate (n + 3) i) - z) := by
    simpa only [hcross] using planar_boundary_coface_interior_cross_product K hcv z hz
      (P i) (P (finRotate (n + 3) i)) (apex i) (hedges i)
      (hcoface i).1 (hcoface i).2.2 (hedge i ▸ (hcoface i).2.1)
      (hapex i).1 (hapex i).2.1 (hapex i).2.2 (by simpa only [hcross] using hd)
  refine ⟨n, P, edge, coface, apex, hPi, hPb, hcycle, hedge, hcoface, huniq, hapex, ?_⟩
  rcases planar_boundary_cycle_uniform_direction_at K hcv z hz n P hPi hedges with hp | hn
  · left
    intro i
    exact (mul_pos_iff.mp (hprod i (hp i).ne')).resolve_right
      (fun h ↦ not_lt_of_ge (hp i).le h.2) |>.1
  · right
    intro i
    exact (mul_pos_iff.mp (hprod i (hn i).ne)).resolve_left
      (fun h ↦ not_lt_of_ge h.2.le (hn i)) |>.1

theorem exists_boundary_cycle_for_coherent_signs
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (number : (ℝ × ℝ) → ℕ) (hnumber : InjOn number K.vertices)
    (sigma : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} → ZMod 2)
    (hsigma : ∀ t u, t ≠ u → ∀ s : Finset (ℝ × ℝ), s.card = 2 →
      s ⊆ t.val → s ⊆ u.val →
      (sigma t + AbstractSimplicialComplex.boundaryFaceParity number t.val s) +
        (sigma u + AbstractSimplicialComplex.boundaryFaceParity number u.val s) = 1) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3))
      (edge : Fin (n + 3) ≃
        {s : Finset (ℝ × ℝ) // s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2})
      (coface : Fin (n + 3) → {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3})
      (eps : ZMod 2),
      Function.Injective P ∧ P.boundary ℝ = frontier K.space ∧
      Equiv.Perm.IsCycle (finRotate (n + 3)) ∧
      (∀ i, (edge i).val = {P i, P (finRotate (n + 3) i)} ∧
        (edge i).val ⊆ (coface i).val) ∧
      ∀ i, sigma (coface i) + Dehn.orderedCofaceParity number (coface i).val
        (P i) (P (finRotate (n + 3) i)) = eps := by
  classical
  obtain ⟨z, hz⟩ := hne
  obtain ⟨n, P, edge, coface, apex, hPi, hPb, hcycle, hedge, hcoface, _, hapex, hdir⟩ :=
    exists_oriented_planar_boundary_cycle_at K hK hcv z hz
  obtain ⟨p, tau, hp, htau, hcancel⟩ := exists_planar_sorted_cross_signs K number hnumber
  have hconn := convex_planar_triangleGraph_connected K hK hcv ⟨z, hz⟩ (by simp)
  obtain ⟨c, hc⟩ := coherent_triangle_signs_global_difference
    K.toPreAbstractSimplicialComplex number hconn sigma tau
    (fun t u htu s hst hsu ↦ hsigma t u htu s.val s.property.2 hst hsu)
    (fun t u htu s hst hsu ↦ hcancel t u htu s.val s.property.2 hst hsu)
  let t (i : Fin (n + 3)) : {t : Finset (ℝ × ℝ) // t ∈ K.faces ∧ t.card = 3} :=
    ⟨coface i, (hcoface i).1, (hcoface i).2.2⟩
  have hpar (i : Fin (n + 3)) :
      tau (t i) + Dehn.orderedCofaceParity number (t i).val
          (P i) (P (finRotate (n + 3) i)) =
        orientationSignParity (SignType.sign
          (planarCross (P (finRotate (n + 3) i) - P i) (apex i - P i))) := by
    rw [htau (t i)]
    have ha : P i ∈ Finset.univ.image (p (t i)) := by
      rw [(hp (t i)).2.1]
      exact (hcoface i).2.1 (hedge i ▸ (by simp))
    have hb : P (finRotate (n + 3) i) ∈ Finset.univ.image (p (t i)) := by
      rw [(hp (t i)).2.1]
      exact (hcoface i).2.1 (hedge i ▸ (by simp))
    have hx : apex i ∈ Finset.univ.image (p (t i)) := by
      rw [(hp (t i)).2.1]
      exact (hapex i).1
    have hab : P i ≠ P (finRotate (n + 3) i) := by
      intro heq
      have hec := (edge i).property.2
      rw [hedge i, heq] at hec
      simp at hec
    have h := planar_numbered_edge_apex_parity number (p (t i)) (hp (t i)).1
      (hp (t i)).2.2.1 (planar_triangle_cross_ne_zero _ (hp (t i)).2.2.2)
      (P i) (P (finRotate (n + 3) i)) (apex i) ha hb hx
      hab (hapex i).2.1.symm (hapex i).2.2.symm
    rw [(hp (t i)).2.1] at h
    exact h.symm
  rcases hdir with hpos | hneg
  · refine ⟨n, P, edge, t, c, hPi, hPb, hcycle,
      fun i ↦ ⟨hedge i, (hcoface i).2.1⟩, ?_⟩
    intro i
    have hh := hpar i
    rw [sign_pos (hpos i)] at hh
    change tau (t i) + _ = 0 at hh
    linear_combination (norm := ring_nf) hc (t i) + hh
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, neg_zero]
  · refine ⟨n, P, edge, t, c + 1, hPi, hPb, hcycle,
      fun i ↦ ⟨hedge i, (hcoface i).2.1⟩, ?_⟩
    intro i
    have hh := hpar i
    rw [sign_neg (hneg i)] at hh
    change tau (t i) + _ = 1 at hh
    linear_combination (norm := ring_nf) hc (t i) + hh
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, neg_zero]

def unitSquareSide (i : Fin 4) (r : ℝ) : ℝ × ℝ :=
  ![(r, 0), (1, r), (1 - r, 1), (0, 1 - r)] i

theorem unitSquareSide_injective (i : Fin 4) : Function.Injective (unitSquareSide i) := by
  intro r s h
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h
  · have hh := congrArg Prod.fst h
    change 1 - r = 1 - s at hh
    linarith
  · have hh := congrArg Prod.snd h
    change 1 - r = 1 - s at hh
    linarith

theorem unitSquareSide_isFinitePL (i : Fin 4) :
    FinitePiecewiseAffineOn (unitSquareSide i) (Icc (0 : ℝ) 1) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  let a : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineMap.lineMap (unitSquareSide i 0) (unitSquareSide i 1)
  have ha : ∀ r, a r = unitSquareSide i r := by
    intro r
    fin_cases i <;> ext <;> simp [a, unitSquareSide, ContinuousAffineMap.coe_lineMap_eq,
      AffineMap.lineMap_apply] <;> ring
  exact ⟨J, hJ, hJs, (J.affineOnFaces_affine a).congr (fun r _ ↦ ha r)⟩

theorem unitSquareSide_mem_square (i : Fin 4) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    unitSquareSide i r ∈ PeriodicSquare.squareCarrier 1 := by
  fin_cases i <;> simp [unitSquareSide, PeriodicSquare.squareCarrier] <;>
    constructor <;> linarith [hr.1, hr.2]

theorem unitSquareSide_coordinate (i : Fin 4) (r : ℝ) :
    ![(unitSquareSide i r).2 = 0, (unitSquareSide i r).1 = 1,
      (unitSquareSide i r).2 = 1, (unitSquareSide i r).1 = 0] i := by
  fin_cases i <;> simp [unitSquareSide]

theorem unitSquareSide_image_Icc (i : Fin 4) :
    unitSquareSide i '' Icc (0 : ℝ) 1 =
      {x ∈ PeriodicSquare.squareCarrier 1 | ![x.2 = 0, x.1 = 1, x.2 = 1, x.1 = 0] i} := by
  apply Subset.antisymm
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨unitSquareSide_mem_square i hr, unitSquareSide_coordinate i r⟩
  · rintro ⟨x, y⟩ ⟨hx, hside⟩
    change (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) at hx
    fin_cases i
    · change y = 0 at hside
      exact ⟨x, hx.1, by simp [unitSquareSide, hside]⟩
    · change x = 1 at hside
      exact ⟨y, hx.2, by simp [unitSquareSide, hside]⟩
    · change y = 1 at hside
      exact ⟨1 - x, ⟨by linarith [hx.1.2], by linarith [hx.1.1]⟩,
        by simp [unitSquareSide, hside]⟩
    · change x = 0 at hside
      exact ⟨1 - y, ⟨by linarith [hx.2.2], by linarith [hx.2.1]⟩,
        by simp [unitSquareSide, hside]⟩

theorem unitSquareSide_mem_frontier (i : Fin 4) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    unitSquareSide i r ∈ frontier (PeriodicSquare.squareCarrier 1) := by
  refine ⟨subset_closure (unitSquareSide_mem_square i hr), ?_⟩
  rw [PeriodicSquare.squareCarrier, interior_prod_eq, interior_Icc]
  fin_cases i <;> simp [unitSquareSide]

theorem unitSquare_frontier_edge_side
    (L : SimplicialComplex ℝ (ℝ × ℝ))
    (hLs : L.space = PeriodicSquare.squareCarrier 1) (a b : ℝ × ℝ)
    (he : {a, b} ∈ (L.frontierSubcomplex L.space).faces) :
    ∃ (i : Fin 4) (r s : ℝ), r ∈ Icc (0 : ℝ) 1 ∧ s ∈ Icc (0 : ℝ) 1 ∧
      a = unitSquareSide i r ∧ b = unitSquareSide i s := by
  have ha : a ∈ PeriodicSquare.squareCarrier 1 :=
    hLs ▸ L.subset_space he.1 (by simp)
  have hb : b ∈ PeriodicSquare.squareCarrier 1 :=
    hLs ▸ L.subset_space he.1 (by simp)
  change (0 ≤ a.1 ∧ a.1 ≤ 1) ∧ (0 ≤ a.2 ∧ a.2 ≤ 1) at ha
  change (0 ≤ b.1 ∧ b.1 ≤ 1) ∧ (0 ≤ b.2 ∧ b.2 ≤ 1) at hb
  have hm : midpoint ℝ a b ∈ frontier (PeriodicSquare.squareCarrier 1) := by
    rw [← hLs]
    apply he.2
    exact (convex_convexHull ℝ _).midpoint_mem
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
  by_cases hy0 : a.2 = 0 ∧ b.2 = 0
  · exact ⟨0, a.1, b.1, ha.1, hb.1,
      by ext <;> simp [unitSquareSide, hy0.1],
      by ext <;> simp [unitSquareSide, hy0.2]⟩
  by_cases hx1 : a.1 = 1 ∧ b.1 = 1
  · exact ⟨1, a.2, b.2, ha.2, hb.2,
      by ext <;> simp [unitSquareSide, hx1.1],
      by ext <;> simp [unitSquareSide, hx1.2]⟩
  by_cases hy1 : a.2 = 1 ∧ b.2 = 1
  · exact ⟨2, 1 - a.1, 1 - b.1, ⟨by linarith [ha.1.2], by linarith [ha.1.1]⟩,
      ⟨by linarith [hb.1.2], by linarith [hb.1.1]⟩,
      by ext <;> simp [unitSquareSide, hy1.1],
      by ext <;> simp [unitSquareSide, hy1.2]⟩
  by_cases hx0 : a.1 = 0 ∧ b.1 = 0
  · exact ⟨3, 1 - a.2, 1 - b.2, ⟨by linarith [ha.2.2], by linarith [ha.2.1]⟩,
      ⟨by linarith [hb.2.2], by linarith [hb.2.1]⟩,
      by ext <;> simp [unitSquareSide, hx0.1],
      by ext <;> simp [unitSquareSide, hx0.2]⟩
  exfalso
  apply hm.2
  rw [PeriodicSquare.squareCarrier, interior_prod_eq, interior_Icc]
  have hxmin : 0 < (a.1 + b.1) / 2 := by
    by_contra h
    apply hx0
    constructor <;> linarith [ha.1.1, hb.1.1]
  have hxmax : (a.1 + b.1) / 2 < 1 := by
    by_contra h
    apply hx1
    constructor <;> linarith [ha.1.2, hb.1.2]
  have hymin : 0 < (a.2 + b.2) / 2 := by
    by_contra h
    apply hy0
    constructor <;> linarith [ha.2.1, hb.2.1]
  have hymax : (a.2 + b.2) / 2 < 1 := by
    by_contra h
    apply hy1
    constructor <;> linarith [ha.2.2, hb.2.2]
  simpa [midpoint_eq_smul_add, div_eq_mul_inv, mul_comm, add_mul] using
    (And.intro (And.intro hxmin hxmax) (And.intro hymin hymax))

theorem unitSquareSide_cross_center (i : Fin 4) (r s : ℝ) :
    planarCross (unitSquareSide i s - unitSquareSide i r)
      (((1 / 2 : ℝ), (1 / 2 : ℝ)) - unitSquareSide i r) = (s - r) / 2 := by
  fin_cases i <;> simp [unitSquareSide, planarCross] <;> ring

theorem unitSquare_center_interior :
    (((1 / 2 : ℝ), (1 / 2 : ℝ))) ∈ interior (PeriodicSquare.squareCarrier 1) := by
  rw [PeriodicSquare.squareCarrier, interior_prod_eq, interior_Icc]
  norm_num

theorem unitSquare_convex : Convex ℝ (PeriodicSquare.squareCarrier 1) :=
  (convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)

theorem planar_boundary_cycle_square_side_order
    (K : SimplicialComplex ℝ (ℝ × ℝ))
    (hKs : K.space = PeriodicSquare.squareCarrier 1)
    (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3)) (hPi : Function.Injective P)
    (hedge : ∀ j, {P j, P (finRotate (n + 3) j)} ∈
      (K.frontierSubcomplex K.space).faces) :
    (∀ i j r s, P j = unitSquareSide i r →
      P (finRotate (n + 3) j) = unitSquareSide i s → r < s) ∨
    (∀ i j r s, P j = unitSquareSide i r →
      P (finRotate (n + 3) j) = unitSquareSide i s → s < r) := by
  have hcv : Convex ℝ K.space := hKs.symm ▸ unitSquare_convex
  have hz : (((1 / 2 : ℝ), (1 / 2 : ℝ))) ∈ interior K.space :=
    hKs.symm ▸ unitSquare_center_interior
  have hcross (a b : ℝ × ℝ) :
      planarCross (a - ((1 / 2 : ℝ), (1 / 2 : ℝ)))
          (b - ((1 / 2 : ℝ), (1 / 2 : ℝ))) =
        planarCross (b - a) (((1 / 2 : ℝ), (1 / 2 : ℝ)) - a) := by
    dsimp [planarCross]
    ring
  rcases planar_boundary_cycle_uniform_direction_at K hcv _ hz n P hPi hedge with hp | hn
  · left
    intro i j r s hr hs
    have h := hp j
    rw [hr, hs, hcross, unitSquareSide_cross_center] at h
    linarith
  · right
    intro i j r s hr hs
    have h := hn j
    rw [hr, hs, hcross, unitSquareSide_cross_center] at h
    linarith

omit [FiniteDimensional ℝ E] in
theorem OriginalRefinementCoherentSigns.exists_square_boundary_cycle [DecidableEq E]
    {K : SimplicialComplex ℝ E} {number : E → ℕ} {sourceSign : Finset E → ZMod 2}
    {L : SimplicialComplex ℝ (ℝ × ℝ)} {refinedNumber : (ℝ × ℝ) → ℕ}
    {F : (ℝ × ℝ) → E}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F)
    (hL : L.faces.Finite) (hLs : L.space = PeriodicSquare.squareCarrier 1)
    (hnumber : InjOn refinedNumber L.vertices) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3))
      (edge : Fin (n + 3) ≃
        {s : Finset (ℝ × ℝ) // s ∈ (L.frontierSubcomplex L.space).faces ∧ s.card = 2})
      (coface : Fin (n + 3) → {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3})
      (eps : ZMod 2),
      Function.Injective P ∧ P.boundary ℝ = frontier L.space ∧
      Equiv.Perm.IsCycle (finRotate (n + 3)) ∧
      (∀ i, (edge i).val = {P i, P (finRotate (n + 3) i)} ∧
        (edge i).val ⊆ (coface i).val) ∧
      ∀ i, O.sign (coface i) + Dehn.orderedCofaceParity refinedNumber (coface i).val
        (P i) (P (finRotate (n + 3) i)) = eps := by
  apply exists_boundary_cycle_for_coherent_signs L hL (hLs.symm ▸ unitSquare_convex)
    ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), hLs.symm ▸ unitSquare_center_interior⟩
    refinedNumber hnumber O.sign O.coherent

omit [FiniteDimensional ℝ E] in
theorem OriginalRefinementCoherentSigns.exists_ccw_square_boundary_sign [DecidableEq E]
    {K : SimplicialComplex ℝ E} {number : E → ℕ} {sourceSign : Finset E → ZMod 2}
    {L : SimplicialComplex ℝ (ℝ × ℝ)} {refinedNumber : (ℝ × ℝ) → ℕ}
    {F : (ℝ × ℝ) → E}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F)
    (hL : L.faces.Finite) (hLs : L.space = PeriodicSquare.squareCarrier 1)
    (hnumber : InjOn refinedNumber L.vertices) :
    ∃ eps : ZMod 2,
      ∀ (t : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3})
        (i : Fin 4) (r s : ℝ),
        {unitSquareSide i r, unitSquareSide i s} ∈ (L.frontierSubcomplex L.space).faces →
        {unitSquareSide i r, unitSquareSide i s} ⊆ t.val → r < s →
        O.sign t + Dehn.orderedCofaceParity refinedNumber t.val
          (unitSquareSide i r) (unitSquareSide i s) = eps := by
  classical
  have hcv : Convex ℝ L.space := hLs.symm ▸ unitSquare_convex
  have hz : (((1 / 2 : ℝ), (1 / 2 : ℝ))) ∈ interior L.space :=
    hLs.symm ▸ unitSquare_center_interior
  obtain ⟨p, tau, hp, htau, hcancel⟩ :=
    exists_planar_sorted_cross_signs L refinedNumber hnumber
  have hconn := convex_planar_triangleGraph_connected L hL hcv ⟨_, hz⟩ (by simp)
  obtain ⟨c, hc⟩ := coherent_triangle_signs_global_difference
    L.toPreAbstractSimplicialComplex refinedNumber hconn O.sign tau
    (fun t u htu e hst hsu ↦ O.coherent t u htu e.val e.property.2 hst hsu)
    (fun t u htu e hst hsu ↦ hcancel t u htu e.val e.property.2 hst hsu)
  refine ⟨c, ?_⟩
  intro t i r s he het hrs
  have hab : unitSquareSide i r ≠ unitSquareSide i s :=
    fun h ↦ hrs.ne (unitSquareSide_injective i h)
  obtain ⟨x, hx, hxt⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨het, by simp [hab, t.property.2]⟩
  have hxne : x ≠ unitSquareSide i r ∧ x ≠ unitSquareSide i s := by simpa using hx
  have hxm : x ∈ t.val := hxt ▸ Finset.mem_insert_self _ _
  have hcenter : 0 < planarCross (unitSquareSide i s - unitSquareSide i r)
      (((1 / 2 : ℝ), (1 / 2 : ℝ)) - unitSquareSide i r) := by
    rw [unitSquareSide_cross_center]
    linarith
  have hprod := planar_boundary_coface_interior_cross_product L hcv _ hz
    (unitSquareSide i r) (unitSquareSide i s) x he t.property.1 t.property.2
    het hxm hxne.1 hxne.2 hcenter.ne'
  have hpos : 0 < planarCross (unitSquareSide i s - unitSquareSide i r)
      (x - unitSquareSide i r) := (mul_pos_iff_of_pos_right hcenter).mp hprod
  have ha : unitSquareSide i r ∈ Finset.univ.image (p t) := by
    rw [(hp t).2.1]
    exact het (by simp)
  have hb : unitSquareSide i s ∈ Finset.univ.image (p t) := by
    rw [(hp t).2.1]
    exact het (by simp)
  have hpx : x ∈ Finset.univ.image (p t) := by rwa [(hp t).2.1]
  have hpar := planar_numbered_edge_apex_parity refinedNumber (p t) (hp t).1
    (hp t).2.2.1 (planar_triangle_cross_ne_zero _ (hp t).2.2.2)
    (unitSquareSide i r) (unitSquareSide i s) x ha hb hpx hab hxne.1.symm hxne.2.symm
  rw [(hp t).2.1, sign_pos hpos] at hpar
  change 0 = _ + _ at hpar
  rw [← htau t] at hpar
  linear_combination (norm := ring_nf) hc t - hpar
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, neg_zero]

namespace OriginalPrimalCutDiskData

open PreAbstractSimplicialComplex.ModTwoCochains

variable [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

theorem marked_square_side_chart
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (C : (PeriodicSquare.squareCarrier 1) ≃ₜ A.carrier)
    (f : (ℝ × ℝ) → ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
    (hf : FinitePiecewiseAffineOn f (PeriodicSquare.squareCarrier 1))
    (hval : ∀ x, f x.val = (C x).val)
    (hmark : ∀ (i : Fin 4) (x : PeriodicSquare.squareCarrier 1),
      (C x).val ∈ A.longBoundaryArc i ↔
        ![x.val.2 = 0, x.val.1 = 1, x.val.2 = 1, x.val.1 = 0] i)
    (i : Fin 4) :
    FinitePiecewiseAffineOn (f ∘ unitSquareSide i) (Icc (0 : ℝ) 1) ∧
      InjOn (f ∘ unitSquareSide i) (Icc (0 : ℝ) 1) ∧
      (f ∘ unitSquareSide i) '' Icc (0 : ℝ) 1 = A.longBoundaryArc i ∧
      f (unitSquareSide i 0) = A.gapCenter (i - 1) ∧
      f (unitSquareSide i 1) = A.gapCenter i := by
  have hmap : MapsTo (unitSquareSide i) (Icc (0 : ℝ) 1)
      (PeriodicSquare.squareCarrier 1) := fun _ hr ↦ unitSquareSide_mem_square i hr
  have hfi : InjOn f (PeriodicSquare.squareCarrier 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (C.injective (Subtype.ext
      ((hval ⟨x, hx⟩).symm.trans (hxy.trans (hval ⟨y, hy⟩)))))
  have himage : (f ∘ unitSquareSide i) '' Icc (0 : ℝ) 1 = A.longBoundaryArc i := by
    apply Subset.antisymm
    · rintro _ ⟨r, hr, rfl⟩
      rw [Function.comp_apply, hval ⟨unitSquareSide i r, hmap hr⟩]
      exact (hmark i _).mpr (unitSquareSide_coordinate i r)
    · intro y hy
      have hyr : y ∈ A.rim := by
        rw [← A.longBoundaryArcs_cover]
        exact mem_iUnion.mpr ⟨i, hy⟩
      have hyA : y ∈ A.carrier := A.disk.1 hyr
      obtain ⟨x, hx⟩ := C.surjective ⟨y, hyA⟩
      have hxside := (hmark i x).mp (by simpa only [hx] using hy)
      obtain ⟨r, hr, hrx⟩ := (unitSquareSide_image_Icc i).symm.subset ⟨x.property, hxside⟩
      exact ⟨r, hr, by
        change f (unitSquareSide i r) = y
        rw [hrx, hval x]
        exact congrArg Subtype.val hx⟩
  have hfinish : f (unitSquareSide i 1) = A.gapCenter i := by
    apply (A.longBoundaryArc_inter_next hbound i).subset
    rw [hval ⟨unitSquareSide i 1, hmap (by norm_num : (1 : ℝ) ∈ Icc 0 1)⟩]
    constructor
    · exact (hmark i _).mpr (unitSquareSide_coordinate i 1)
    · apply (hmark (i + 1) _).mpr
      fin_cases i <;> simp [unitSquareSide]
  have hstart : f (unitSquareSide i 0) = A.gapCenter (i - 1) := by
    apply (A.longBoundaryArc_inter_next hbound (i - 1)).subset
    rw [hval ⟨unitSquareSide i 0, hmap (by norm_num : (0 : ℝ) ∈ Icc 0 1)⟩]
    constructor
    · apply (hmark (i - 1) _).mpr
      fin_cases i <;> simp [unitSquareSide]
    · simpa only [sub_add_cancel] using (hmark i _).mpr (unitSquareSide_coordinate i 0)
  exact ⟨hf.comp (unitSquareSide_isFinitePL i) hmap,
    fun r hr s hs h ↦ unitSquareSide_injective i (hfi (hmap hr) (hmap hs) h),
    himage, hstart, hfinish⟩

theorem exists_marked_square_bridge_parameters
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (C : (PeriodicSquare.squareCarrier 1) ≃ₜ A.carrier)
    (f : (ℝ × ℝ) → ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
    (hf : FinitePiecewiseAffineOn f (PeriodicSquare.squareCarrier 1))
    (hval : ∀ x, f x.val = (C x).val)
    (hmark : ∀ (i : Fin 4) (x : PeriodicSquare.squareCarrier 1),
      (C x).val ∈ A.longBoundaryArc i ↔
        ![x.val.2 = 0, x.val.1 = 1, x.val.2 = 1, x.val.1 = 0] i)
    (i : Fin 4) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ β < 1 ∧
      f (unitSquareSide i α) = A.bridgeBegin i ∧
      f (unitSquareSide i β) = A.bridgeEnd i ∧
      (f ∘ unitSquareSide i) '' Icc α β = A.boundaryBridge i ∧
      InjOn (A.sourceMap ∘ (f ∘ unitSquareSide i)) (Icc α β) ∧
      ∀ r ∈ Icc (0 : ℝ) 1,
        (f (unitSquareSide i r) ∈ A.boundaryBridge i \ {A.bridgeBegin i, A.bridgeEnd i} ↔
          r ∈ Ioo α β) := by
  let g := f ∘ unitSquareSide i
  obtain ⟨hg, hgi, hgs, hg0, hg1⟩ :=
    A.marked_square_side_chart hbound C f hf hval hmark i
  have hleft : IsFinitePLBallPair ℝ (A.gapSpokes (i - 1)).right
      {g 0, A.bridgeBegin i} := by
    simpa only [g, Function.comp_apply, hg0, sub_add_cancel] using
      (A.gapSpokes (i - 1)).right_ball
  have hright : IsFinitePLBallPair ℝ (A.gapSpokes i).left {A.bridgeEnd i, g 1} := by
    simpa only [g, Function.comp_apply, hg1, pair_comm] using (A.gapSpokes i).left_ball
  have hdis : Disjoint (A.gapSpokes (i - 1)).right (A.gapSpokes i).left :=
    (A.gapSpokes_different_disjoint (by fin_cases i <;> decide)).mono
      subset_union_right subset_union_left
  obtain ⟨α, β, hα, hαβ, hβ, hga, hgb, hmiddle⟩ := ordered_middle_parameters hg hgi
    hleft (A.boundaryBridge_interval i) hright
    (hgs.symm ▸ (subset_union_left.trans subset_union_left))
    (hgs.symm ▸ (subset_union_right.trans subset_union_left))
    (hgs.symm ▸ subset_union_right) hdis
  have hsub : Icc α β ⊆ Icc (0 : ℝ) 1 :=
    fun _ hx ↦ ⟨hα.le.trans hx.1, hx.2.trans hβ.le⟩
  have hαu : α ∈ Icc (0 : ℝ) 1 := hsub ⟨le_rfl, hαβ.le⟩
  have hβu : β ∈ Icc (0 : ℝ) 1 := hsub ⟨hαβ.le, le_rfl⟩
  refine ⟨α, β, hα, hαβ, hβ, hga, hgb, hmiddle.symm, ?_, ?_⟩
  · intro r hr s hs hrs
    exact hgi (hsub hr) (hsub hs) (A.sourceMap_injOn_boundaryBridge i
      (hmiddle.symm ▸ mem_image_of_mem g hr) (hmiddle.symm ▸ mem_image_of_mem g hs) hrs)
  · intro r hr
    change (g r ∈ A.boundaryBridge i \ {A.bridgeBegin i, A.bridgeEnd i} ↔ r ∈ Ioo α β)
    constructor
    · intro h
      obtain ⟨s, hs, hsr⟩ := hmiddle.subset h.1
      have heq : s = r := hgi (hsub hs) hr hsr
      subst s
      refine ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩
      · intro he
        exact h.2 (Or.inl (he ▸ hga))
      · intro he
        exact h.2 (Or.inr (he ▸ hgb))
    · intro h
      refine ⟨hmiddle.symm ▸ mem_image_of_mem g ⟨h.1.le, h.2.le⟩, ?_⟩
      intro he
      rcases he with he | he
      · have heq := hgi hr hαu (he.trans hga.symm)
        exact h.1.ne' heq
      · have heq := hgi hr hβu (he.trans hgb.symm)
        exact h.2.ne heq

end OriginalPrimalCutDiskData

end PoincareConjecture.M76.OriginalTriangleCopies
