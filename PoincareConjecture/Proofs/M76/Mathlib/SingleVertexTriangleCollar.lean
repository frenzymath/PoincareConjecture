import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleLabels
import PoincareConjecture.Proofs.M76.Mathlib.GeometricExceptionalEdgeCollar
import PoincareConjecture.Proofs.M76.Mathlib.RegularTriangleSlabCollar
import PoincareConjecture.Proofs.M76.Mathlib.StrictCrossingPointIncidence











set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]









theorem exists_singleVertex_triangle_collar_with_geometry (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z)
    {s : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (hnontriv : ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q) :
    ∃ (S : Set (E × ℝ)) (T : Set E) (H : S ≃ₜ T), H.IsFinitePL ∧
      ((q ∉ s ∧ T = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β}) ∨
        ∃ u v : E, (s : Set E) = insert q {u, v} ∧ A u < 0 ∧ β < A v ∧
          q ≠ A.zeroCrossing u v ∧ S = TaperedStrip.segmentDomain q (A.zeroCrossing u v) β ∧
          T = convexHull ℝ (insert q ({A.zeroCrossing u v,
            A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∧
          ∀ p : S, (H p : E) = (p : E × ℝ).1 +
            (p : E × ℝ).2 • A.heightRay (A.zeroCrossing u v) v) ∧
      ((q ∉ s ∧ S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
        ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
          (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
          S = TaperedStrip.segmentDomain q w β) ∧
      (S ⊆ (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∧
      (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, (x, (0 : ℝ)) ∈ S) ∧
      (∀ p ∈ S, ∀ t ∈ Icc 0 p.2, (p.1, t) ∈ S) ∧
      (T ⊆ convexHull ℝ (s : Set E)) ∧
      (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ p : S, (p : E × ℝ).2 = 0 → (H p : E) = (p : E × ℝ).1) ∧
      (∀ p : S, (p : E × ℝ).1 = q → (p : E × ℝ).2 = 0) ∧
      (∀ e : Finset E, e.card = 2 → e ⊆ s → ∀ p : S,
        (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔
          (H p : E) ∈ convexHull ℝ (e : Set E)) ∧
      ∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q →
        ∃ t : ℝ, 0 < t ∧ (x, t) ∈ S := by
  classical
  have hvertex (z : E) (hz : z ∈ s) : z ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hz) (Finset.singleton_nonempty z)
  by_cases hqs : q ∈ s
  · have hnezero (z : E) (hz : z ∈ s) (hzq : z ≠ q) : A z ≠ 0 := by
      rcases hreg z (hvertex z hz) hzq with h | h
      · exact h.ne
      · exact (hβ.trans h).ne'
    obtain ⟨u, v, hlabels, hu, hv⟩ :=
      A.exists_exceptional_triangle_labels hsc hqs hAq hnezero hnontriv
    have humem : u ∈ s := by rw [hlabels]; simp
    have hvmem : v ∈ s := by rw [hlabels]; simp
    have hqu : q ≠ u := by intro h; exact hu.ne (h.symm ▸ hAq)
    have hqv : q ≠ v := by intro h; exact hv.ne' (h.symm ▸ hAq)
    have huv : u ≠ v := by intro h; exact hu.not_gt (h.symm ▸ hv)
    have hβv : β < A v := (hreg v (hvertex v hvmem) hqv.symm).resolve_left hv.not_gt
    have hvec : Function.Injective ![q, u, v] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hrange : range ![q, u, v] ⊆ (s : Set E) := by
      rintro z ⟨i, rfl⟩
      fin_cases i
      · exact hqs
      · exact humem
      · exact hvmem
    have hind : AffineIndependent ℝ ![q, u, v] :=
      ((K.indep hs).mono hrange).of_set_of_injective hvec
    obtain ⟨H, hH, hformula, hheight, hbottom, hsub, hsection, hedge⟩ :=
      A.exists_exceptional_triangle_geometric_edge_collar_with_formula hind hAq hu hv hβ hβv
    let w := A.zeroCrossing u v
    have hstrad : A.StraddlesZero ({u, v} : Finset E) := ⟨u, v, hu, hv, by simp⟩
    have hef : ({u, v} : Finset E) ∈ K.faces :=
      K.down_closed hs (by rw [hlabels]; simp) (by simp)
    have hsw : A.straddlingPoint {u, v} hstrad = w :=
      A.straddlingPoint_eq_zeroCrossing hstrad hu hv (by simp)
    have hqw : q ≠ w := by
      apply Ne.symm
      rw [← hsw]
      exact K.straddlingPoint_ne_vertex A hef hstrad hqK
    have hset : (s : Set E) = insert q {u, v} := by rw [hlabels]; simp
    have hsec : convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w := by
      rw [hset]
      exact hsection
    refine ⟨TaperedStrip.segmentDomain q w β, _, H, hH, ?_, ?_, ?_, ?_, ?_, ?_,
      hheight, hbottom, ?_, ?_, ?_⟩
    · exact Or.inr ⟨u, v, hset, hu, hβv, hqw, rfl, rfl, hformula⟩
    · refine Or.inr ⟨w, hqs, hqw, ?_, hsec, rfl⟩
      have herase : s.erase q = {u, v} := by
        rw [hlabels]
        simp [hqu, hqv]
      rw [← Finset.coe_erase, herase, ← hsw]
      exact (A.straddlingPoint_mem {u, v} hstrad).1
    · intro p hp
      have h := TaperedStrip.segmentDomain_subset_product hβ hp
      exact ⟨hsec.symm ▸ h.1, h.2⟩
    · intro x hx
      exact (TaperedStrip.mk_zero_mem_segmentDomain_iff hβ).mpr (hsec ▸ hx)
    · intro p hp t ht
      obtain ⟨a, ha, hbase, htop⟩ := (TaperedStrip.mem_segmentDomain_iff hβ).mp hp
      exact (TaperedStrip.mem_segmentDomain_iff hβ).mpr
        ⟨a, ha, hbase, ht.1, ht.2.trans htop.2⟩
    · rw [hset]
      exact hsub
    · intro p hpq
      have hpval : (p : E × ℝ) = (q, (p : E × ℝ).2) := Prod.ext hpq rfl
      exact (TaperedStrip.mk_left_mem_segmentDomain_iff hqw hβ).mp (hpval ▸ p.property)
    · intro e he hes p
      rw [hlabels] at hes
      exact hedge e he hes p
    · intro x hx hxq
      have hxseg : x ∈ segment ℝ q w := hsec ▸ hx
      rw [segment_eq_image_lineMap] at hxseg
      obtain ⟨a, ha, hax⟩ := hxseg
      have ha0 : a ≠ 0 := by
        intro hazero
        apply hxq
        simpa only [hazero, AffineMap.lineMap_apply_zero] using hax.symm
      have hapos : 0 < a := lt_of_le_of_ne ha.1 ha0.symm
      exact ⟨β * a, mul_pos hβ hapos, (TaperedStrip.mem_segmentDomain_iff hβ).mpr
        ⟨a, ha, hax.symm, mul_nonneg hβ.le ha.1, le_rfl⟩⟩
  · have hlocal (z : E) (hz : z ∈ s) : A z < 0 ∨ β < A z :=
      hreg z (hvertex z hz) (fun h => hqs (h ▸ hz))
    have hmeet : (convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β}).Nonempty := by
      obtain ⟨x, hx, _⟩ := hnontriv
      exact ⟨x, hx.1, by change A x ∈ Icc 0 β; rw [hx.2]; exact ⟨le_rfl, hβ.le⟩⟩
    obtain ⟨H, hH, hheight, hbottom, hedge⟩ :=
      A.exists_regular_triangle_collar (K.indep hs) hsc hβ hlocal hmeet
    refine ⟨_, _, H, hH, Or.inl ⟨hqs, rfl⟩, Or.inl ⟨hqs, rfl⟩, Subset.rfl, ?_, ?_,
      inter_subset_left,
      hheight, ?_, ?_, hedge, ?_⟩
    · intro x hx
      exact ⟨hx, le_rfl, hβ.le⟩
    · intro p hp t ht
      exact ⟨hp.1, ht.1, ht.2.trans hp.2.2⟩
    · intro p hp
      have hpeq : p = ⟨((p : E × ℝ).1, 0), p.property.1, le_rfl, hβ.le⟩ :=
        Subtype.ext (Prod.ext rfl hp)
      rw [hpeq]
      exact hbottom _ p.property.1
    · intro p hpq
      have hqmem : q ∈ convexHull ℝ (s : Set E) := hpq ▸ p.property.1.1
      exact (hqs ((K.vertex_mem_convexHull_iff hqK hs).mp hqmem)).elim
    · intro x hx _
      exact ⟨β, hβ, hx, hβ.le, le_rfl⟩








theorem exists_singleVertex_triangle_collar_with_source (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z)
    {s : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (hnontriv : ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q) :
    ∃ (S : Set (E × ℝ)) (T : Set E) (H : S ≃ₜ T), H.IsFinitePL ∧
      ((q ∉ s ∧ S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
        ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
          (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
          S = TaperedStrip.segmentDomain q w β) ∧
      (S ⊆ (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∧
      (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, (x, (0 : ℝ)) ∈ S) ∧
      (∀ p ∈ S, ∀ t ∈ Icc 0 p.2, (p.1, t) ∈ S) ∧
      (T ⊆ convexHull ℝ (s : Set E)) ∧
      (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ p : S, (p : E × ℝ).2 = 0 → (H p : E) = (p : E × ℝ).1) ∧
      (∀ p : S, (p : E × ℝ).1 = q → (p : E × ℝ).2 = 0) ∧
      (∀ e : Finset E, e.card = 2 → e ⊆ s → ∀ p : S,
        (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔
          (H p : E) ∈ convexHull ℝ (e : Set E)) ∧
      ∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q →
        ∃ t : ℝ, 0 < t ∧ (x, t) ∈ S := by
  obtain ⟨S, T, H, hH, _, hrest⟩ :=
    K.exists_singleVertex_triangle_collar_with_geometry A hqK hAq hβ hreg hs hsc hnontriv
  exact ⟨S, T, H, hH, hrest⟩








theorem exists_singleVertex_triangle_collar (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z)
    {s : Finset E} (hs : s ∈ K.faces) (hsc : s.card = 3)
    (hnontriv : ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q) :
    ∃ (S : Set (E × ℝ)) (T : Set E) (H : S ≃ₜ T), H.IsFinitePL ∧
      (S ⊆ (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∧
      (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, (x, (0 : ℝ)) ∈ S) ∧
      (∀ p ∈ S, ∀ t ∈ Icc 0 p.2, (p.1, t) ∈ S) ∧
      (T ⊆ convexHull ℝ (s : Set E)) ∧
      (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ p : S, (p : E × ℝ).2 = 0 → (H p : E) = (p : E × ℝ).1) ∧
      (∀ p : S, (p : E × ℝ).1 = q → (p : E × ℝ).2 = 0) ∧
      (∀ e : Finset E, e.card = 2 → e ⊆ s → ∀ p : S,
        (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔
          (H p : E) ∈ convexHull ℝ (e : Set E)) ∧
      ∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q →
        ∃ t : ℝ, 0 < t ∧ (x, t) ∈ S := by
  obtain ⟨S, T, H, hH, _, hrest⟩ :=
    K.exists_singleVertex_triangle_collar_with_source A hqK hAq hβ hreg hs hsc hnontriv
  exact ⟨S, T, H, hH, hrest⟩

end Geometry.SimplicialComplex
