import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.LineCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalEndpoint
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals











set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem halfInterval_endpoint_in_chart
    {X : Type*} [TopologicalSpace X]
    (I B Q : OpenPartialHomeomorph X V3)
    (hB : I.symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hQ : I.symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {y : X} (hyI : y ∈ I.source) (hyB : y ∈ B.source) (hyQ : y ∈ Q.source)
    (D : Set X) {z : V3} {r : ℝ} (hzy : z ≠ B y) (hr : 0 < r)
    (hsection : (B '' (D ∩ B.source)) ∩ Metric.ball (B y) r =
      AffineMap.lineMap (B y) z '' Ico (0 : ℝ) (r / dist (B y) z))
    (hemb : Topology.IsEmbedding (AffineMap.lineMap (B y) z : ℝ → V3)) :
    ∃ u : V3, u ≠ Q y ∧ ∀ᶠ x in 𝓝 (Q y),
      x ∈ Q '' (D ∩ Q.source) ↔ x ∈ segment ℝ (Q y) u := by
  classical
  let C := (I.symm.trans B).symm.trans (I.symm.trans Q)
  have hC : C ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm hB) hQ
  have hyC : B y ∈ C.source := by
    change (B y ∈ B.target ∧ B.symm (B y) ∈ I.source) ∧
      (I (B.symm (B y)) ∈ I.target ∧ I.symm (I (B.symm (B y))) ∈ Q.source)
    simpa only [B.left_inv hyB, I.left_inv hyI] using
      And.intro (And.intro (B.map_source hyB) hyI) (And.intro (I.map_source hyI) hyQ)
  have hCy : C (B y) = Q y := by
    change Q (I.symm (I (B.symm (B y)))) = Q y
    rw [B.left_inv hyB, I.left_inv hyI]
  have hCsymm (x : V3) (hx : x ∈ C.target) : C.symm x = B (Q.symm x) := by
    change B (I.symm (I (Q.symm x))) = B (Q.symm x)
    rw [I.left_inv hx.1.2]
  have hbackB (x : V3) (hx : x ∈ C.target) : Q.symm x ∈ B.source := by
    have hh := hx.2.2
    change I.symm (I (Q.symm x)) ∈ B.source at hh
    rwa [I.left_inv hx.1.2] at hh
  have hchart (x : V3) (hx : x ∈ C.target) :
      x ∈ Q '' (D ∩ Q.source) ↔ C.symm x ∈ B '' (D ∩ B.source) := by
    constructor
    · rintro ⟨v, ⟨hvD, hvQ⟩, rfl⟩
      have hvB : v ∈ B.source := by simpa only [Q.left_inv hvQ] using hbackB (Q v) hx
      exact ⟨v, ⟨hvD, hvB⟩, by rw [hCsymm _ hx, Q.left_inv hvQ]⟩
    · rintro ⟨v, ⟨hvD, hvB⟩, hvx⟩
      have hv : v = Q.symm x := B.injOn hvB (hbackB x hx) (hvx.trans (hCsymm x hx))
      exact ⟨Q.symm x, ⟨hv ▸ hvD, Q.map_target hx.1.1⟩, Q.right_inv hx.1.1⟩
  obtain ⟨R, hR, hyR, hRsource, hfR⟩ :=
    ((mem_piecewiseAffineGroupoid_iff V3 C).mp hC).1 (B y) hyC
  obtain ⟨δ, hδ, hδR⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hyR)
  have hd : 0 < dist (B y) z := dist_pos.mpr hzy.symm
  let c := min (r / dist (B y) z) (δ / dist (B y) z) / 2
  have hm : 0 < min (r / dist (B y) z) (δ / dist (B y) z) :=
    lt_min (div_pos hr hd) (div_pos hδ hd)
  have hc : 0 < c := half_pos hm
  have hcr : c < r / dist (B y) z := (half_lt_self hm).trans_le (min_le_left _ _)
  have hcδ : c < δ / dist (B y) z := (half_lt_self hm).trans_le (min_le_right _ _)
  let f : ℝ →ᴬ[ℝ] V3 := ContinuousAffineMap.lineMap (B y) z
  have hf (t : ℝ) : f t = AffineMap.lineMap (B y) z t := rfl
  have hf0 : f 0 = B y := by rw [hf, AffineMap.lineMap_apply_zero]
  have hdist (t : ℝ) (ht : 0 ≤ t) : dist (f t) (B y) = t * dist (B y) z := by
    simp only [hf, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht]
  have hIR : f '' Icc 0 c ⊆ R.space := by
    rintro _ ⟨t, ht, rfl⟩
    apply interior_subset
    apply hδR
    rw [Metric.mem_ball, hdist t ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 hd.le).trans_lt ((lt_div_iff₀ hd).mp hcδ)
  have hI := isFinitePLBallPair_affine_interval hc f hemb.injective.injOn
  have hCI : IsFinitePLBallPair ℝ (C '' (f '' Icc 0 c)) (C '' {f 0, f c}) :=
    hI.image_of_subset (hfR.finitePiecewiseAffineOn hR) hIR (C.injOn.mono hRsource)
  let V := Metric.ball (B y) (c * dist (B y) z)
  let U := C.target ∩ C.symm ⁻¹' V
  have hU : IsOpen U := C.symm.isOpen_inter_preimage Metric.isOpen_ball
  have hyU : Q y ∈ U := by
    refine ⟨hCy ▸ C.map_source hyC, ?_⟩
    change C.symm (Q y) ∈ V
    rw [← hCy, C.left_inv hyC]
    exact Metric.mem_ball_self (mul_pos hc hd)
  have hVr : V ⊆ Metric.ball (B y) r :=
    Metric.ball_subset_ball ((lt_div_iff₀ hd).mp hcr).le
  have hfull (x : V3) (hx : x ∈ U) :
      x ∈ Q '' (D ∩ Q.source) ↔ x ∈ C '' (f '' Icc 0 c) := by
    rw [hchart x hx.1]
    constructor
    · intro hxD
      obtain ⟨t, ht, htx⟩ := hsection.subset ⟨hxD, hVr hx.2⟩
      have ht' : t < c := by
        have hh : dist (f t) (B y) < c * dist (B y) z := by
          rw [hf, htx]
          exact hx.2
        rw [hdist t ht.1] at hh
        exact (mul_lt_mul_iff_left₀ hd).mp hh
      exact ⟨C.symm x, ⟨t, ⟨ht.1, ht'.le⟩, htx⟩, C.right_inv hx.1⟩
    · rintro ⟨w, ⟨t, ht, rfl⟩, htx⟩
      have htα : t < r / dist (B y) z := ht.2.trans_lt hcr
      have hback : C.symm x = f t := by rw [← htx, C.left_inv (hRsource (hIR ⟨t, ht, rfl⟩))]
      rw [hback]
      exact (hsection.symm.subset ⟨t, ⟨ht.1, htα⟩, rfl⟩).1
  have hyend : Q y ∈ C '' {f 0, f c} := ⟨f 0, Or.inl rfl, by rw [hf0, hCy]⟩
  obtain ⟨u, hu, hlocal⟩ := hCI.exists_segment_germ_of_mem_boundary hyend
  refine ⟨u, hu, ?_⟩
  filter_upwards [hU.mem_nhds hyU, hlocal] with x hx hxlocal
  exact (hfull x hx).trans hxlocal



theorem HasOriginalEdgeCofaceCharts.exists_surface_contact_segment_germ_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hAtlas : ∀ y ∈ S, ∃ i, y ∈ (e i).source)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hyQ : y ∈ Q.source) :
    ∃ u : V3, u ≠ Q y ∧ ∀ᶠ x in 𝓝 (Q y),
      x ∈ Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source) ↔
        x ∈ segment ℝ (Q y) u := by
  obtain ⟨B, z, r, hB, hyB, hzy, hr, _, _, hsection, hemb, _⟩ :=
    h.exists_triangle_halfInterval hgi hSV hpq hwp hwq ht hy
  obtain ⟨i, hye⟩ := hAtlas y hy.1
  exact halfInterval_endpoint_in_chart (e i) B Q (hB i) (hQ i) hye hyB hyQ
    (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E))) hzy hr hsection hemb



theorem HasOriginalEdgeCofaceCharts.exists_surface_contact_segment_germ_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hAtlas : ∀ y ∈ S, ∃ i, y ∈ (e i).source) (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E)))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ u : V3, u ≠ Q y ∧ ∀ᶠ x in 𝓝 (Q y),
      x ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) ↔
        x ∈ segment ℝ (Q y) u := by
  have hyQ : y ∈ Q.source := by
    obtain ⟨x, hx, rfl⟩ := hy.2
    exact hmap (convexHull_mono has hx)
  have hphysical : ∃ u : V3, u ≠ Q y ∧ ∀ᶠ x in 𝓝 (Q y),
      x ∈ Q '' (S ∩ (g '' convexHull ℝ (s : Set E)) ∩ Q.source) ↔
        x ∈ segment ℝ (Q y) u := by
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp ha2
    obtain ⟨w, hw, rfl⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨has, by rw [Finset.card_pair hpq, hs3]⟩
    have hwp : w ≠ p := fun he => hw (he.symm ▸ Finset.mem_insert_self _ _)
    have hwq : w ≠ q := fun he => hw (he.symm ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
    have hy' : y ∈ S ∩ (g '' segment ℝ p q) := by
      simpa only [Finset.coe_pair, convexHull_pair] using hy
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      h.exists_surface_contact_segment_germ_in_chart hAtlas hgi hSV hpq hwp hwq hs hy' Q hQ hyQ
  have himage : convexHull ℝ (A '' (s : Set E)) = (Q ∘ g) '' convexHull ℝ (s : Set E) :=
    (A.toAffineMap.image_convexHull _).symm.trans (image_congr hA).symm
  have hfull : Q '' (S ∩ (g '' convexHull ℝ (s : Set E)) ∩ Q.source) =
      Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) := by
    ext x
    constructor
    · rintro ⟨z, ⟨⟨hzS, v, hv, hvz⟩, hzQ⟩, hzx⟩
      exact ⟨⟨z, ⟨hzS, hzQ⟩, hzx⟩, himage.symm.subset
        ⟨v, hv, by change Q (g v) = x; rw [hvz, hzx]⟩⟩
    · rintro ⟨⟨z, ⟨hzS, hzQ⟩, hzx⟩, hxt⟩
      obtain ⟨v, hv, hvx⟩ := himage.subset hxt
      have hvz : g v = z := Q.injOn (hmap hv) hzQ (hvx.trans hzx.symm)
      exact ⟨z, ⟨⟨hzS, v, hv, hvz⟩, hzQ⟩, hzx⟩
  simpa only [hfull] using hphysical




theorem HasOriginalEdgeCofaceCharts.ncard_surface_contact_neighborSet_eq_one_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hAtlas : ∀ y ∈ S, ∃ i, y ∈ (e i).source) (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E)))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite) (hyG : Q y ∈ G.vertices)
    (hlocal : ∀ᶠ x in 𝓝 (Q y), x ∈ G.space ↔
      x ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E))) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨Q y, hyG⟩).ncard = 1 := by
  obtain ⟨u, hu, hgerm⟩ := h.exists_surface_contact_segment_germ_of_affine_chart
    hAtlas hs hs3 has ha2 hgi hSV hy Q hQ A hmap hA
  apply G.ncard_neighborSet_eq_one_of_local_segment_at hG hyG hu
  filter_upwards [hlocal, hgerm] with x hx hxg
  exact hx.trans hxg

end PoincareConjecture.M76

