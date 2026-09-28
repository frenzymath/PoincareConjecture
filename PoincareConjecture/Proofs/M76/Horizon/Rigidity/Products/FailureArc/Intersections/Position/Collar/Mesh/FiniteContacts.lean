import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.RegularLevel
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.GeneralPosition.FiniteNormalParameters

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh

theorem exists_finite_moving_contacts_normal_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2)
    {z rho : E → ℝ} (hz : K.AffineOnFaces z) (hrho : K.AffineOnFaces rho)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c ∈ Ioo (0 : ℝ) epsilon,
      (∀ v ∈ K.vertices, z v + c * rho v = 0 → z v = 0 ∧ rho v = 0) ∧
      (K.space ∩ {x | z x + c * rho x = 0 ∧ rho x ≠ 0}).Finite := by
  classical
  have hV := (K.finite_vertices_of_finite_faces hK).subset
    (inter_subset_left : K.vertices ∩ {v | rho v ≠ 0} ⊆ K.vertices)
  obtain ⟨c, hc, hgeneric⟩ := hV.exists_pos_height_perturbation_parameter z rho
    (fun v hv hvzero => (hv.2 hvzero).elim) hepsilon
  have hverts (v : E) (hv : v ∈ K.vertices) (heq : z v + c * rho v = 0) :
      z v = 0 ∧ rho v = 0 := by
    have hr : rho v = 0 := by
      by_contra hn
      exact hgeneric v ⟨hv, hn⟩ heq
    exact ⟨by simpa only [hr, mul_zero, add_zero] using heq, hr⟩
  refine ⟨c, hc, hverts, ?_⟩
  have hface (s : Finset E) (hs : s ∈ K.faces) :
      (convexHull ℝ (s : Set E) ∩ {x | z x + c * rho x = 0 ∧ rho x ≠ 0}).Finite := by
    obtain ⟨A, hA⟩ := hz s hs
    obtain ⟨B, hB⟩ := hrho s hs
    let F : E →ᵃ[ℝ] ℝ := A.toAffineMap + c • B.toAffineMap
    have hF (x : E) (hx : x ∈ convexHull ℝ (s : Set E)) :
        F x = z x + c * rho x := by
      change A x + c * B x = z x + c * rho x
      rw [← hA hx, ← hB hx]
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    have hbound := hcard s hs
    rcases (show s.card = 1 ∨ s.card = 2 by omega) with hs1 | hs2
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hs1
      apply (finite_singleton p).subset
      simpa only [Finset.coe_singleton, convexHull_singleton] using
        (inter_subset_left : convexHull ℝ (({p} : Finset E) : Set E) ∩
          {x | z x + c * rho x = 0 ∧ rho x ≠ 0} ⊆ _)
    · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs2
      by_cases hdiff : F p ≠ F q
      · apply Set.Subsingleton.finite
        intro x hx y hy
        have hline {w : E} (hw : w ∈ convexHull ℝ (({p, q} : Finset E) : Set E)) :
            w ∈ affineSpan ℝ ({p, q} : Set E) :=
          convexHull_subset_affineSpan _ (by simpa only [Finset.coe_pair] using hw)
        have hx0 : F x = 0 := (hF x hx.1).trans hx.2.1
        have hy0 : F y = 0 := (hF y hy.1).trans hy.2.1
        exact (F.eq_zeroCrossing_of_mem_affineSpan hdiff (hline hx.1) hx0).trans
          (F.eq_zeroCrossing_of_mem_affineSpan hdiff (hline hy.1) hy0).symm
      · apply finite_empty.subset
        intro x hx
        exfalso
        have hpH : p ∈ convexHull ℝ (({p, q} : Finset E) : Set E) :=
          subset_convexHull ℝ _ (by simp)
        have hqH : q ∈ convexHull ℝ (({p, q} : Finset E) : Set E) :=
          subset_convexHull ℝ _ (by simp)
        have hpV : p ∈ K.vertices := K.down_closed hs (by simp) (Finset.singleton_nonempty p)
        have hqV : q ∈ K.vertices := K.down_closed hs (by simp) (Finset.singleton_nonempty q)
        have heq : F p = F q := not_not.mp hdiff
        have hxseg : x ∈ segment ℝ p q := by
          simpa only [Finset.coe_pair, convexHull_pair] using hx.1
        have hFx : F x = F p := by
          have hm := mem_image_of_mem F hxseg
          rwa [image_segment, ← heq, segment_same, mem_singleton_iff] at hm
        have hp0 : F p = 0 := hFx.symm.trans ((hF x hx.1).trans hx.2.1)
        have hq0 : F q = 0 := heq.symm.trans hp0
        have hpfix := hverts p hpV ((hF p hpH).symm.trans hp0)
        have hqfix := hverts q hqV ((hF q hqH).symm.trans hq0)
        have hb0 : B x = 0 := by
          have hm := mem_image_of_mem B.toAffineMap hxseg
          rw [image_segment] at hm
          change B x ∈ segment ℝ (B p) (B q) at hm
          rw [← hB hpH, ← hB hqH, hpfix.2, hqfix.2,
            segment_same, mem_singleton_iff] at hm
          exact hm
        exact hx.2.2 ((hB hx.1).trans hb0)
  apply (hK.biUnion hface).subset
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx.1
  exact mem_iUnion₂.mpr ⟨s, hs, hxs, hx.2⟩

theorem exists_finite_contacts_normal_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2)
    {z rho : E → ℝ} (hz : K.AffineOnFaces z) (hrho : K.AffineOnFaces rho)
    (hfixed : (K.space ∩ {x | z x = 0 ∧ rho x = 0}).Finite)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c ∈ Ioo (0 : ℝ) epsilon,
      (∀ v ∈ K.vertices, z v + c * rho v = 0 → z v = 0 ∧ rho v = 0) ∧
      (K.space ∩ {x | z x + c * rho x = 0}).Finite := by
  obtain ⟨c, hc, hvertices, hfinite⟩ :=
    exists_finite_moving_contacts_normal_parameter K hK hcard hz hrho hepsilon
  refine ⟨c, hc, hvertices, (hfinite.union hfixed).subset ?_⟩
  intro x hx
  by_cases hr : rho x = 0
  · exact Or.inr ⟨hx.1,
      by simpa only [mem_ofPred_eq, hr, mul_zero, add_zero] using hx.2, hr⟩
  · exact Or.inl ⟨hx.1, hx.2, hr⟩

end PoincareConjecture.M76.CollarMesh
