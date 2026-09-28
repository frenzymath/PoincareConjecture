import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.LineCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalGerm
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals











set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem halfInterval_germ_in_chart
    {X : Type*} [TopologicalSpace X]
    (I B Q : OpenPartialHomeomorph X V3)
    (hB : I.symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hQ : I.symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {y : X} (hyI : y ∈ I.source) (hyB : y ∈ B.source) (hyQ : y ∈ Q.source)
    (D : Set X) {z : V3} {r : ℝ} (hzy : z ≠ B y) (hr : 0 < r)
    (hsection : (B '' (D ∩ B.source)) ∩ Metric.ball (B y) r =
      AffineMap.lineMap (B y) z '' Ico (0 : ℝ) (r / dist (B y) z))
    (hemb : Topology.IsEmbedding (AffineMap.lineMap (B y) z : ℝ → V3)) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (D ∩ Q.source)) ∩ U, x ≠ Q y →
        ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x, a ∈ Q '' (D ∩ Q.source) ↔
            a ∈ segment ℝ x u ∪ segment ℝ x v := by
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
  refine ⟨U, hU, hyU, fun _ hx => hx.1.1.1, ?_⟩
  intro x hx hxy
  have hxI : x ∈ C '' (f '' Icc 0 c) \ C '' {f 0, f c} := by
    refine ⟨(hfull x hx.2).mp hx.1, ?_⟩
    rintro ⟨w, hw, hwx⟩
    rcases hw with rfl | rfl
    · exact hxy (hwx.symm.trans (by rw [hf0, hCy]))
    · have hh := hx.2.2
      change dist (C.symm x) (B y) < c * dist (B y) z at hh
      rw [← hwx, C.left_inv (hRsource (hIR ⟨c, ⟨hc.le, le_rfl⟩, rfl⟩)),
        hdist c hc.le] at hh
      exact lt_irrefl _ hh
  obtain ⟨u, v, hu, hv, hinter, hlocal⟩ :=
    IsFinitePLBallPair.exists_two_segment_germ hCI hxI
  refine ⟨u, v, hu, hv, hinter, ?_⟩
  filter_upwards [hU.mem_nhds hx.2, hlocal] with a ha halocal
  exact (hfull a ha).trans halocal




theorem HasOriginalEdgeCofaceCharts.exists_surface_contact_two_segment_germs_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hcover : ∀ y ∈ S, ∃ i, y ∈ (e i).source)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hyQ : y ∈ Q.source) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source)) ∩ U,
        x ≠ Q y → ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  obtain ⟨B, z, r, hB, hyB, hzy, hr, _, _, hsection, hemb, _⟩ :=
    h.exists_triangle_halfInterval hgi hSV hpq hwp hwq ht hy
  obtain ⟨i, hye⟩ := hcover y hy.1
  exact halfInterval_germ_in_chart (e i) B Q (hB i) (hQ i) hye hyB hyQ
    (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E))) hzy hr hsection hemb




theorem HasOriginalEdgeCofaceCharts.exists_surface_contact_two_segment_germs_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hcover : ∀ y ∈ S, ∃ i, y ∈ (e i).source)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E))) ∩ U,
        x ≠ Q y → ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  have hseg : segment ℝ p q ⊆ convexHull ℝ ({w, p, q} : Set E) := by
    rw [← convexHull_pair]
    exact convexHull_mono (by intro x hx; exact Or.inr hx)
  have hyQ : y ∈ Q.source := by
    obtain ⟨x, hx, rfl⟩ := hy.2
    exact hmap (hseg hx)
  obtain ⟨U, hU, hyU, hUQ, hgerm⟩ :=
    h.exists_surface_contact_two_segment_germs_in_chart hcover hgi hSV hpq hwp hwq ht hy Q hQ hyQ
  have himage : convexHull ℝ (A '' ({w, p, q} : Set E)) =
      (Q ∘ g) '' convexHull ℝ ({w, p, q} : Set E) :=
    (A.toAffineMap.image_convexHull _).symm.trans (image_congr hA).symm
  have hfull : Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source) =
      Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) := by
    ext x
    constructor
    · rintro ⟨z, ⟨⟨hzS, u, hu, huz⟩, hzQ⟩, hzx⟩
      exact ⟨⟨z, ⟨hzS, hzQ⟩, hzx⟩, himage.symm.subset
        ⟨u, hu, by change Q (g u) = x; rw [huz, hzx]⟩⟩
    · rintro ⟨⟨z, ⟨hzS, hzQ⟩, hzx⟩, hxt⟩
      obtain ⟨u, hu, hux⟩ := himage.subset hxt
      have huz : g u = z := Q.injOn (hmap hu) hzQ (hux.trans hzx.symm)
      exact ⟨z, ⟨⟨hzS, u, hu, huz⟩, hzQ⟩, hzx⟩
  exact ⟨U, hU, hyU, hUQ, by simpa only [hfull] using hgerm⟩

private theorem original_edge_contact_not_mem_triangle_intrinsicInterior
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (hgi : InjOn g K.space) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ g '' segment ℝ p q)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    Q y ∉ intrinsicInterior ℝ (convexHull ℝ (A '' ({w, p, q} : Set E))) := by
  classical
  let s : Finset E := {w, p, q}
  let K₀ : SimplicialComplex ℝ E :=
    { faces := {a | a ∈ K.faces ∧ a ⊆ s}
      indep := fun ha => K.indep ha.1
      isRelLowerSet_faces := by
        intro a ha
        exact ⟨K.nonempty_of_mem_faces ha.1, fun b hba hb =>
          ⟨K.down_closed ha.1 hba hb, hba.trans ha.2⟩⟩
      inter_subset_convexHull := fun ha hb => K.inter_subset_convexHull ha.1 hb.1 }
  have hs : s ∈ K₀.faces := ⟨ht, Finset.Subset.rfl⟩
  have hKs : K₀.space = convexHull ℝ ({w, p, q} : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := SimplicialComplex.mem_space_iff.mp hx
      simpa only [s, Finset.coe_insert, Finset.coe_singleton] using convexHull_mono ha.2 hxa
    · simpa only [s, Finset.coe_insert, Finset.coe_singleton] using K₀.convexHull_subset_space hs
  have hK : convexHull ℝ ({w, p, q} : Set E) ⊆ K.space := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using K.convexHull_subset_space ht
  have hai : InjOn A K₀.space := by
    intro x hx z hz heq
    have hx' := hKs.subset hx
    have hz' := hKs.subset hz
    apply hgi (hK hx') (hK hz')
    exact Q.injOn (hmap hx') (hmap hz') ((hA hx').trans (heq.trans (hA hz').symm))
  have hf : K₀.AffineOnFaces A := K₀.affineOnFaces_affine A
  let T := hf.embeddedImage hai
  have hsT : s.image A ∈ T.faces :=
    (hf.image_mem_embeddedImage_iff hai (K₀.subset_space hs)).mpr hs
  have ha : ({p, q} : Finset E) ∈ K₀.faces :=
    K₀.down_closed hs (by simp [s]) (Finset.insert_nonempty _ _)
  have haT : ({p, q} : Finset E).image A ∈ T.faces :=
    (hf.image_mem_embeddedImage_iff hai (K₀.subset_space ha)).mpr ha
  have hyA : Q y ∈ convexHull ℝ (({p, q} : Finset E).image A : Set V3) := by
    obtain ⟨z, hz, rfl⟩ := hy
    have hzK : z ∈ convexHull ℝ (({p, q} : Finset E) : Set E) := by
      simpa only [Finset.coe_pair, convexHull_pair] using hz
    rw [show Q (g z) = A z from hA (hKs.subset (K₀.convexHull_subset_space ha hzK)),
      Finset.coe_image, ← hf.image_convexHull ha]
    exact mem_image_of_mem A hzK
  intro hyint
  have hyint' : Q y ∈ intrinsicInterior ℝ (convexHull ℝ (s.image A : Set V3)) := by
    simpa only [Finset.coe_image, s, Finset.coe_insert, Finset.coe_singleton] using hyint
  have hsub := T.subset_of_mem_intrinsicInterior_face hsT haT hyint' hyA
  have hwim : A w ∈ s.image A := Finset.mem_image.mpr ⟨w, by simp [s], rfl⟩
  obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp (hsub hwim)
  have hvw' : v = w := hai (K₀.subset_space ha hv) (K₀.subset_space hs (by simp [s])) hvw
  have hwmem : w ∈ ({p, q} : Finset E) := hvw' ▸ hv
  simp only [Finset.mem_insert, Finset.mem_singleton, hwp, hwq, or_self] at hwmem




theorem HasOriginalEdgeCofaceCharts.exists_surface_interior_two_segment_germs_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hcover : ∀ y ∈ S, ∃ i, y ∈ (e i).source)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
          intrinsicInterior ℝ (convexHull ℝ (A '' ({w, p, q} : Set E)))) ∩ U,
        ∃ u v : V3, u ≠ x ∧ v ≠ x ∧ segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  obtain ⟨U, hU, hyU, hUQ, hgerm⟩ :=
    h.exists_surface_contact_two_segment_germs_of_affine_chart hcover hgi hSV
      hpq hwp hwq ht hy Q hQ A hmap hA
  refine ⟨U, hU, hyU, hUQ, ?_⟩
  intro x hx
  apply hgerm x ⟨⟨hx.1.1, intrinsicInterior_subset hx.1.2⟩, hx.2⟩
  intro hxy
  exact original_edge_contact_not_mem_triangle_intrinsicInterior hgi hwp hwq ht hy.2
    Q A hmap hA (hxy ▸ hx.1.2)

end PoincareConjecture.M76

