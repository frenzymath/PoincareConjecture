import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexTriangleCollar
import PoincareConjecture.Proofs.M76.Mathlib.ResidualCollarRoof
import PoincareConjecture.Proofs.M76.Mathlib.ResidualOppositeEdge
import PoincareConjecture.Proofs.M76.Mathlib.ResidualTriangleFinitePL
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlabPartition
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.ResidualLevelScaling
import PoincareConjecture.Proofs.M76.Mathlib.ResidualContactScaling










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]










theorem exists_triangle_collar_residual_with_contacts (A : E →ᵃ[ℝ] ℝ)
    {s : Finset E} {q : E} (hAq : A q = 0) {β : ℝ} (hβ : 0 < β)
    {S : Set (E × ℝ)} {T : Set E} (H : S ≃ₜ T) (hH : H.IsFinitePL)
    (hgeometry : (q ∉ s ∧ T = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β}) ∨
      ∃ u v : E, (s : Set E) = insert q {u, v} ∧ A u < 0 ∧ β < A v ∧
        q ≠ A.zeroCrossing u v ∧ S = TaperedStrip.segmentDomain q (A.zeroCrossing u v) β ∧
        T = convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∧
        ∀ p : S, (H p : E) = (p : E × ℝ).1 +
          (p : E × ℝ).2 • A.heightRay (A.zeroCrossing u v) v)
    (hsource : (q ∉ s ∧ S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
      ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
        (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        S = TaperedStrip.segmentDomain q w β)
    (hheight : ∀ p, A (H p) = (p : E × ℝ).2) :
    ∃ (R : Set E) (J : SimplicialComplex ℝ E), J.faces.Finite ∧ J.space = R ∧
      T ∪ R = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β} ∧
      R ∩ {x | A x = 0} ⊆ {q} ∧
      (∀ e : Finset E, e.card = 2 → e ⊆ s → q ∉ e →
        ∀ x ∈ R ∩ convexHull ℝ (e : Set E), A x = β) ∧
      (q ∉ s → ∀ c ∈ Ioo 0 β, R ∩ {x | A x = c} = ∅) ∧
      (q ∈ s → ∀ c ∈ Ioc 0 β, R ∩ {x | A x = c} =
        homothety q (c / β) '' (convexHull ℝ (s : Set E) ∩ {x | A x = β})) ∧
      (q ∈ s → ∀ c ∈ Ioc 0 β, (T ∩ R) ∩ {x | A x = c} =
        homothety q (c / β) '' (convexHull ℝ ((s : Set E) \ {q}) ∩ {x | A x = β})) ∧
      ∀ a : E →ᴬ[ℝ] ℝ,
        (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, a x ∈ Icc 0 β) →
        S = {p : E × ℝ | p.1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (a p.1)} →
        ∀ p : S, (H p : E) ∈ R ↔ (p : E × ℝ).2 = a (p : E × ℝ).1 := by
  classical
  rcases hgeometry with ⟨hqs, hT⟩ | ⟨u, v, hs, hu, hβv, hqw, hS, hT, hformula⟩
  · have hS : S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β := by
      rcases hsource with ⟨_, hS⟩ | ⟨w, hq, _⟩
      · exact hS
      · exact (hqs hq).elim
    obtain ⟨f, ⟨L, hL, hLT, _⟩, _⟩ := hH.symm
    obtain ⟨J, hJ, hJs⟩ := L.exists_finite_affineLevel_complex hL A β
    refine ⟨T ∩ {x | A x = β}, J, hJ, by simpa only [hLT] using hJs,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [union_eq_self_of_subset_right inter_subset_left, hT]
    · intro x hx
      exact (hβ.ne' (hx.1.2.symm.trans hx.2)).elim
    · intro e _ _ _ x hx
      exact hx.1.2
    · intro _ c hc
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hc.2.ne (hx.2.symm.trans hx.1.2)
    · intro hq
      exact (hqs hq).elim
    · intro hq
      exact (hqs hq).elim
    · intro a habound haband p
      have hp : (p : E × ℝ).1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} :=
        (hS.subset p.property).1
      have htop : ((p : E × ℝ).1, β) ∈ S := hS.symm.subset ⟨hp, hβ.le, le_rfl⟩
      have ha : a (p : E × ℝ).1 = β :=
        le_antisymm (habound _ hp).2
          (show ((p : E × ℝ).1, β) ∈ {p : E × ℝ |
            p.1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} ∧ p.2 ∈ Icc 0 (a p.1)}
            from haband.subset htop).2.2
      change ((H p : E) ∈ T ∧ A (H p) = β) ↔ _
      rw [hheight, ha]
      exact and_iff_right (H p).property
  · let w := A.zeroCrossing u v
    let R := convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E))
    have hv : 0 < A v := hβ.trans hβv
    have hw : A w = 0 := A.zeroCrossing_apply (hu.trans hv).ne
    have hwv : A v ≠ A w := by rw [hw]; exact hv.ne'
    have hqv : A v ≠ A q := by rw [hAq]; exact hv.ne'
    have htopw : A (A.edgeLevel w v β) = β := A.apply_edgeLevel hwv β
    have htopq : A (A.edgeLevel q v β) = β := A.apply_edgeLevel hqv β
    obtain ⟨G, hG, _, _⟩ := A.exists_zeroApex_residual_chart hqw hAq hw hβ hβv
    obtain ⟨f, ⟨J, hJ, hJR, _⟩, _⟩ := hG.symm
    have hunion : T ∪ R = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β} := by
      rw [hT, hs]
      exact (A.exceptional_triangle_slab_partition hAq hu hβ hβv hqw).1
    have hzero : R ∩ {x | A x = 0} = {q} :=
      A.convexHull_zero_apex_pair_inter_zero_of_pos hAq
        (by rwa [htopw]) (by rwa [htopq])
    refine ⟨R, J, hJ, hJR, hunion, hzero.subset, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he hes hqe x hx
      have hsfin : s = {q, u, v} := Finset.coe_injective (by simpa using hs)
      rw [hsfin] at hes
      rcases Finset.eq_pair_of_subset_triple he hes with heq | heq | heq
      · exact (hqe (by rw [heq]; simp)).elim
      · exact (hqe (by rw [heq]; simp)).elim
      · have hxuv : x ∈ R ∩ segment ℝ u v := by
          simpa only [heq, Finset.coe_pair, convexHull_pair] using hx
        have hxval : x = A.edgeLevel w v β :=
          mem_singleton_iff.mp
            ((A.exceptional_residual_opposite_edge_intersection hAq hu hβ hβv hqw).subset hxuv)
        rw [hxval, htopw]
    · intro hqs
      exact (hqs (by change q ∈ (s : Set E); rw [hs]; exact mem_insert _ _)).elim
    · intro _ c hc
      have htopSection : R ∩ {x | A x = β} =
          convexHull ℝ (s : Set E) ∩ {x | A x = β} := by
        ext x
        constructor
        · intro hx
          exact ⟨((hunion.subset (Or.inr hx.1)).1), hx.2⟩
        · intro hx
          have hxslab : x ∈ T ∪ R := hunion.symm.subset
            ⟨hx.1, by change A x ∈ Icc 0 β; rw [hx.2]; exact ⟨hβ.le, le_rfl⟩⟩
          refine ⟨?_, hx.2⟩
          rcases hxslab with hxT | hxR
          · rw [hT, ← A.zeroApexCoordinates_image q w v hw hβ] at hxT
            obtain ⟨p, hp, rfl⟩ := hxT
            have hp2 : p.2 = β :=
              (A.apply_zeroApexCoordinates hAq hw hv.ne' p).symm.trans hx.2
            exact (A.zeroApexCoordinates_mem_residual_iff hqw hAq hw hβ hβv hp).mpr
              (le_antisymm hp.2.2 (by nlinarith [hp.1.2]))
          · exact hxR
      have htopBase : R ∩ {x | A x = β} =
          segment ℝ (A.edgeLevel w v β) (A.edgeLevel q v β) := by
        simpa [hβ.ne'] using
          A.zeroApex_residual_level_homothety hAq hw hβ hβv ⟨hβ.le, le_rfl⟩
      rw [← htopSection, htopBase]
      exact A.zeroApex_residual_level_homothety hAq hw hβ hβv ⟨hc.1.le, hc.2⟩
    · intro _ c hc
      have huq : u ≠ q := fun h => hu.ne (h ▸ hAq)
      have hvq : v ≠ q := fun h => hv.ne' (h ▸ hAq)
      have hremove : (s : Set E) \ {q} = {u, v} := by
        rw [hs]
        ext x
        simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨hx, hxq⟩
          exact hx.resolve_left hxq
        · intro hx
          exact ⟨Or.inr hx, by rcases hx with rfl | rfl <;> assumption⟩
      rw [hT, hremove, convexHull_pair]
      exact A.exceptional_collar_residual_contact_homothety hAq hu hβ hβv hqw
        ⟨hc.1.le, hc.2⟩
    · intro a habound haband p
      have hsection : convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w := by
        rw [hs]
        exact A.convexHull_zero_apex_pair_inter_zero hAq hu hv
      have hqsec : q ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} :=
        hsection.symm.subset (left_mem_segment ℝ q w)
      have hwsec : w ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} :=
        hsection.symm.subset (right_mem_segment ℝ q w)
      have hqtop : (q, a q) ∈ S := haband.symm.subset ⟨hqsec, (habound q hqsec).1, le_rfl⟩
      have haq : a q = 0 :=
        (TaperedStrip.mk_left_mem_segmentDomain_iff hqw hβ).mp (hS.subset hqtop)
      have hwtop : (w, β) ∈ S := by
        rw [hS]
        apply (TaperedStrip.mem_segmentDomain_iff hβ).mpr
        exact ⟨1, ⟨zero_le_one, le_rfl⟩, (lineMap_apply_one q w).symm,
          hβ.le, by simp⟩
      have haw : a w = β := le_antisymm (habound w hwsec).2
        (show (w, β) ∈ {p : E × ℝ |
          p.1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} ∧ p.2 ∈ Icc 0 (a p.1)}
          from haband.subset hwtop).2.2
      rw [hformula]
      exact A.geometric_collar_mem_residual_iff hqw hAq hw hβ hβv a.toAffineMap haq haw
        (hS.subset p.property)





theorem exists_triangle_collar_residual_with_levels (A : E →ᵃ[ℝ] ℝ)
    {s : Finset E} {q : E} (hAq : A q = 0) {β : ℝ} (hβ : 0 < β)
    {S : Set (E × ℝ)} {T : Set E} (H : S ≃ₜ T) (hH : H.IsFinitePL)
    (hgeometry : (q ∉ s ∧ T = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β}) ∨
      ∃ u v : E, (s : Set E) = insert q {u, v} ∧ A u < 0 ∧ β < A v ∧
        q ≠ A.zeroCrossing u v ∧ S = TaperedStrip.segmentDomain q (A.zeroCrossing u v) β ∧
        T = convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∧
        ∀ p : S, (H p : E) = (p : E × ℝ).1 +
          (p : E × ℝ).2 • A.heightRay (A.zeroCrossing u v) v)
    (hsource : (q ∉ s ∧ S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
      ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
        (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        S = TaperedStrip.segmentDomain q w β)
    (hheight : ∀ p, A (H p) = (p : E × ℝ).2) :
    ∃ (R : Set E) (J : SimplicialComplex ℝ E), J.faces.Finite ∧ J.space = R ∧
      T ∪ R = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β} ∧
      R ∩ {x | A x = 0} ⊆ {q} ∧
      (∀ e : Finset E, e.card = 2 → e ⊆ s → q ∉ e →
        ∀ x ∈ R ∩ convexHull ℝ (e : Set E), A x = β) ∧
      (q ∉ s → ∀ c ∈ Ioo 0 β, R ∩ {x | A x = c} = ∅) ∧
      (q ∈ s → ∀ c ∈ Ioc 0 β, R ∩ {x | A x = c} =
        homothety q (c / β) '' (convexHull ℝ (s : Set E) ∩ {x | A x = β})) ∧
      ∀ a : E →ᴬ[ℝ] ℝ,
        (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, a x ∈ Icc 0 β) →
        S = {p : E × ℝ | p.1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (a p.1)} →
        ∀ p : S, (H p : E) ∈ R ↔ (p : E × ℝ).2 = a (p : E × ℝ).1 := by
  obtain ⟨R, J, hJ, hJR, hfull, hzero, hedge, hmissing, hradial, _, hroof⟩ :=
    A.exists_triangle_collar_residual_with_contacts hAq hβ H hH hgeometry hsource hheight
  exact ⟨R, J, hJ, hJR, hfull, hzero, hedge, hmissing, hradial, hroof⟩






theorem exists_triangle_collar_residual (A : E →ᵃ[ℝ] ℝ)
    {s : Finset E} {q : E} (hAq : A q = 0) {β : ℝ} (hβ : 0 < β)
    {S : Set (E × ℝ)} {T : Set E} (H : S ≃ₜ T) (hH : H.IsFinitePL)
    (hgeometry : (q ∉ s ∧ T = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β}) ∨
      ∃ u v : E, (s : Set E) = insert q {u, v} ∧ A u < 0 ∧ β < A v ∧
        q ≠ A.zeroCrossing u v ∧ S = TaperedStrip.segmentDomain q (A.zeroCrossing u v) β ∧
        T = convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∧
        ∀ p : S, (H p : E) = (p : E × ℝ).1 +
          (p : E × ℝ).2 • A.heightRay (A.zeroCrossing u v) v)
    (hsource : (q ∉ s ∧ S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
      ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
        (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        S = TaperedStrip.segmentDomain q w β)
    (hheight : ∀ p, A (H p) = (p : E × ℝ).2) :
    ∃ (R : Set E) (J : SimplicialComplex ℝ E), J.faces.Finite ∧ J.space = R ∧
      T ∪ R = convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc 0 β} ∧
      R ∩ {x | A x = 0} ⊆ {q} ∧
      (∀ e : Finset E, e.card = 2 → e ⊆ s → q ∉ e →
        ∀ x ∈ R ∩ convexHull ℝ (e : Set E), A x = β) ∧
      ∀ a : E →ᴬ[ℝ] ℝ,
        (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, a x ∈ Icc 0 β) →
        S = {p : E × ℝ | p.1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (a p.1)} →
        ∀ p : S, (H p : E) ∈ R ↔ (p : E × ℝ).2 = a (p : E × ℝ).1 := by
  obtain ⟨R, J, hJ, hJR, hcover, hzero, hedge, _, _, hroof⟩ :=
    A.exists_triangle_collar_residual_with_levels hAq hβ H hH hgeometry hsource hheight
  exact ⟨R, J, hJ, hJR, hcover, hzero, hedge, hroof⟩

end AffineMap
