import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceGerms
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeSphereDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Mathlib.CompatibleSignedPairHalfspace
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private noncomputable def signedCornerCoordinates (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    V3 ≃L[ℝ] C3 :=
  ({ toFun := fun z => ((ε * z 0, z 2), z 1)
     invFun := fun z => ![ε * z.1.1, z.2, z.1.2]
     left_inv := by
       intro z
       rcases hε with rfl | rfl <;> funext i <;> fin_cases i <;> simp
     right_inv := by
       intro z
       rcases hε with rfl | rfl <;> ext <;> simp
     map_add' := by intro z w; ext <;> simp [mul_add]
     map_smul' := by intro a z; ext <;> simp [mul_left_comm] } : V3 ≃ₗ[ℝ] C3).toContinuousLinearEquiv

theorem PLDomain.inter_of_transverse_frontiers
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {A B : Set X}
    (ha : PLDomain e A) (hb : PLDomain e B)
    (hcross : ∀ x ∈ frontier A ∩ frontier B, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ frontier A ↔ H y 0 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier B ↔ H y 1 = 0) :
    PLDomain e (A ∩ B) := by
  refine ⟨ha.cover, ha.compatible, ha.closed.inter hb.closed, ?_⟩
  intro x hx
  have hxAB : x ∈ A ∩ B := (ha.closed.inter hb.closed).frontier_subset hx
  by_cases hxa : x ∈ frontier A
  · by_cases hxb : x ∈ frontier B
    · obtain ⟨H, hxH, hHz, hHe, hHA, hHB⟩ := hcross x ⟨hxa, hxb⟩
      obtain ⟨T, hxT, hTz, hcv, hTH, _, _, hval, _⟩ :=
        H.exists_convex_target_avoiding hxH hHz isClosed_empty (notMem_empty x)
      have hTe (i : ι) : (e i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
        apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
        exact ((hHe i).1.mono ((e i).symm.trans T).open_source
          (fun _ hz => ⟨hz.1, hTH hz.2⟩)).congr (fun z _ => (hval ((e i).symm z)).symm)
      have hTA (y : X) (hy : y ∈ T.source) : y ∈ frontier A ↔ T y 0 = 0 := by
        rw [hval]
        exact hHA y (hTH hy)
      have hTB (y : X) (hy : y ∈ T.source) : y ∈ frontier B ↔ T y 1 = 0 := by
        rw [hval]
        exact hHB y (hTH hy)
      have hAside := halfspace_of_convex_linear_frontier_chart ha.closed ha.closure_interior
        hxa T hxT (ContinuousLinearMap.proj 0) hcv hTA
      have hBside := halfspace_of_convex_linear_frontier_chart hb.closed hb.closure_interior
        hxb T hxT (ContinuousLinearMap.proj 1) hcv hTB
      obtain ⟨ε, hε, hA⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
          ∀ y ∈ T.source, y ∈ A ↔ 0 ≤ ε * T y 0 := by
        rcases hAside with hp | hn
        · exact ⟨1, Or.inl rfl, fun y hy => by simpa using hp y hy⟩
        · exact ⟨-1, Or.inr rfl, fun y hy => by simpa using hn y hy⟩
      obtain ⟨η, hη, hB⟩ : ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
          ∀ y ∈ T.source, y ∈ B ↔ 0 ≤ η * T y 1 := by
        rcases hBside with hp | hn
        · exact ⟨1, Or.inl rfl, fun y hy => by simpa using hp y hy⟩
        · exact ⟨-1, Or.inr rfl, fun y hy => by simpa using hn y hy⟩
      let c := signedCornerCoordinates ε hε
      let C := T.trans c.toHomeomorph.toOpenPartialHomeomorph
      have hC (i : ι) : LocallyPiecewiseAffineOn ((e i).symm.trans C)
          ((e i).symm.trans C).source := by
        have hc : LocallyPiecewiseAffineOn c.toHomeomorph.toOpenPartialHomeomorph
            c.toHomeomorph.toOpenPartialHomeomorph.source :=
          locallyPiecewiseAffineOn_affine c.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ
        have hh : LocallyPiecewiseAffineOn
            (((e i).symm.trans T).trans c.toHomeomorph.toOpenPartialHomeomorph)
            (((e i).symm.trans T).trans c.toHomeomorph.toOpenPartialHomeomorph).source :=
          hc.comp (hTe i).1
        simpa only [C, OpenPartialHomeomorph.trans_assoc] using hh
      apply exists_compatible_halfspace_of_signed_pair e C ⟨hxT, mem_univ _⟩
        (show C x = 0 by change c (T x) = 0; rw [hTz, map_zero]) hC η hη (Or.inr ?_)
      intro y hy
      exact and_congr (hA y hy.1) (hB y hy.1)
    · have hxBi : x ∈ interior B := (mem_interior_iff_notMem_frontier hxAB.2).mpr hxb
      obtain ⟨ell, v, H, hv, hxH, hzero, hHe, hhalf⟩ := ha.halfspace x hxa
      let T := H.restrOpen (interior B) isOpen_interior
      refine ⟨ell, v, T, hv, ⟨hxH, hxBi⟩, hzero, ?_, ?_⟩
      · intro i
        exact (e i).piecewiseAffine_compatible_restrOpen_right H (hHe i) isOpen_interior
      · intro y hy
        exact (and_iff_left (interior_subset hy.2)).trans (hhalf y hy.1)
  · have hxAi : x ∈ interior A := (mem_interior_iff_notMem_frontier hxAB.1).mpr hxa
    have hxb : x ∈ frontier B := by
      by_contra hn
      have hxBi : x ∈ interior B := (mem_interior_iff_notMem_frontier hxAB.2).mpr hn
      exact hx.2 (by rw [interior_inter]; exact ⟨hxAi, hxBi⟩)
    obtain ⟨ell, v, H, hv, hxH, hzero, hHe, hhalf⟩ := hb.halfspace x hxb
    let T := H.restrOpen (interior A) isOpen_interior
    refine ⟨ell, v, T, hv, ⟨hxH, hxAi⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hHe i) isOpen_interior
    · intro y hy
      exact (and_iff_right (interior_subset hy.2)).trans (hhalf y hy.1)

theorem ChartwisePLSphere.exists_lattice_exterior_corner_domains
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S E : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hE : IsCompact E) (heE : PLDomain e E)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0) :
    ∃ Q : Set (LatticeHandleAmbient ι κ L), IsCompact Q ∧ frontier Q = S ∧
      IsUnitBallPair V3 Q S ∧ Q ⊆ interior (latticeHandleDomain ι κ L) ∧
      IsCompact (E ∩ Q) ∧ PLDomain e (E ∩ Q) ∧
      IsCompact (E ∩ (interior Q)ᶜ) ∧ PLDomain e (E ∩ (interior Q)ᶜ) := by
  obtain ⟨Q, hQ, hfront, hpair, hq, hqc, hinside⟩ :=
    s.exists_lattice_ball_domains L he hdim hSR
  have hmeet {W : Set (LatticeHandleAmbient ι κ L)} (hW : PLDomain e W)
      (hf : frontier W = S) : PLDomain e (E ∩ W) := by
    apply heE.inter_of_transverse_frontiers hW
    intro x hx
    obtain ⟨H, hxH, hHz, hHe, hHS, hHE⟩ := hcross x ⟨hf ▸ hx.2, hx.1⟩
    exact ⟨H, hxH, hHz, hHe, hHE, fun y hy => hf ▸ hHS y hy⟩
  exact ⟨Q, hQ, hfront, hpair, hinside, hE.inter_right hQ.isClosed,
    hmeet hq hfront, hE.inter_right isOpen_interior.isClosed_compl,
    hmeet hqc (hq.frontier_closed_exterior.trans hfront)⟩

theorem finitePLBallPair_image_closed_side
    {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace X]
    {d q : Set F} (hd : IsFinitePLBallPair G d q)
    {f : F → X} (hf : ContinuousOn f d) {Q : Set X} (hQ : IsClosed Q)
    (hreg : closure (interior Q) = Q)
    (havoid : Disjoint (f '' (d \ q)) (frontier Q)) :
    (f '' d ⊆ Q ∧ f '' (d \ q) ⊆ interior Q) ∨
      (f '' d ⊆ (interior Q)ᶜ ∧ f '' (d \ q) ⊆ interior (interior Q)ᶜ) := by
  have hconn := hd.isConnected_sdiff.isPreconnected.image f (hf.mono sdiff_subset)
  have hcl : f '' d ⊆ closure (f '' (d \ q)) := by
    have hh : ContinuousOn f (closure (d \ q)) := hd.closure_sdiff.symm ▸ hf
    simpa only [hd.closure_sdiff] using hh.image_closure
  have hav : Disjoint (frontier Qᶜ) (f '' (d \ q)) := by
    rw [frontier_compl]
    exact havoid.symm
  rcases hconn.subset_or_subset_compl_closure hQ.isOpen_compl hav with hout | hin
  · right
    have hext : f '' (d \ q) ⊆ interior (interior Q)ᶜ := by
      rw [interior_compl, hreg]
      exact hout
    exact ⟨hcl.trans (closure_minimal (hext.trans interior_subset) isOpen_interior.isClosed_compl), hext⟩
  · left
    have hint : f '' (d \ q) ⊆ interior Q := by
      simpa only [← interior_eq_compl_closure_compl] using hin
    exact ⟨hcl.trans (closure_minimal (hint.trans interior_subset) hQ), hint⟩

theorem ChartwisePLSphere.exists_original_bigon_corner_domain
    {ι κ α F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S E : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hE : IsCompact E) (heE : PLDomain e E)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
    {d U C : Set F} (hd : IsFinitePLBallPair (ℝ × ℝ) d (U ∪ C))
    {f : F → LatticeHandleAmbient ι κ L}
    (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d) (hfE : MapsTo f d E)
    (hfront : (f '' d) ∩ frontier E = f '' U)
    (hsphere : (f '' d) ∩ S = f '' C) :
    ∃ N : Set (LatticeHandleAmbient ι κ L),
      IsCompact N ∧ PLDomain e N ∧ N ⊆ E ∧ MapsTo f d N ∧
      (∀ z ∈ d, f z ∈ frontier N ↔ z ∈ U ∪ C) ∧
      frontier N = N ∩ (frontier E ∪ S) := by
  obtain ⟨Q, hQ, hQS, hpair, hq, hqc, hQR⟩ := s.exists_lattice_ball_domains L he hdim hSR
  have havoid : Disjoint (f '' (d \ (U ∪ C))) (frontier Q) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    obtain ⟨y, hy, heq⟩ := hsphere.subset ⟨⟨z, hz.1, rfl⟩, hQS ▸ hx⟩
    exact hz.2 (Or.inr (hfi (hd.1 (Or.inr hy)) hz.1 heq ▸ hy))
  have hside := finitePLBallPair_image_closed_side hd hf.continuousOn hQ.isClosed hq.closure_interior havoid
  obtain ⟨W, hW, hWS, hfW, hfWi⟩ :
      ∃ W : Set (LatticeHandleAmbient ι κ L), PLDomain e W ∧ frontier W = S ∧
        f '' d ⊆ W ∧ f '' (d \ (U ∪ C)) ⊆ interior W := by
    rcases hside with hi | ho
    · exact ⟨Q, hq, hQS, hi⟩
    · exact ⟨(interior Q)ᶜ, hqc, hq.frontier_closed_exterior.trans hQS, ho⟩
  have hN : PLDomain e (E ∩ W) := by
    apply heE.inter_of_transverse_frontiers hW
    intro x hx
    obtain ⟨H, hxH, hHz, hHe, hHS, hHE⟩ := hcross x ⟨hWS ▸ hx.2, hx.1⟩
    exact ⟨H, hxH, hHz, hHe, hHE, fun y hy => hWS ▸ hHS y hy⟩
  have hfN : MapsTo f d (E ∩ W) := fun z hz => ⟨hfE hz, hfW ⟨z, hz, rfl⟩⟩
  refine ⟨E ∩ W, hE.inter_right hW.closed, hN, inter_subset_left, hfN, ?_, ?_⟩
  · intro z hz
    constructor
    · intro hn
      by_contra hzq
      have hzE : f z ∈ interior E := by
        apply (mem_interior_iff_notMem_frontier (hfE hz)).mpr
        intro hx
        obtain ⟨y, hy, heq⟩ := hfront.subset ⟨⟨z, hz, rfl⟩, hx⟩
        exact hzq (Or.inl (hfi (hd.1 (Or.inl hy)) hz heq ▸ hy))
      exact hn.2 (by rw [interior_inter]; exact ⟨hzE, hfWi ⟨z, ⟨hz, hzq⟩, rfl⟩⟩)
    · intro hzq
      refine ⟨subset_closure (hfN hz), ?_⟩
      intro hint
      rcases hzq with hu | hc
      · exact (hfront.symm.subset ⟨z, hu, rfl⟩).2.2 (interior_mono inter_subset_left hint)
      · have hs : f z ∈ frontier W := hWS.symm ▸ (hsphere.symm.subset ⟨z, hc, rfl⟩).2
        exact hs.2 (interior_mono inter_subset_right hint)
  · apply Subset.antisymm
    · intro x hx
      refine ⟨hN.closed.frontier_subset hx, ?_⟩
      rcases (frontier_inter_subset E W) hx with h | h
      · exact Or.inl h.1
      · exact Or.inr (hWS ▸ h.2)
    · rintro x ⟨hx, hxf⟩
      refine ⟨subset_closure hx, ?_⟩
      intro hint
      rcases hxf with he | hs
      · exact he.2 (interior_mono inter_subset_left hint)
      · exact (hWS.symm ▸ hs).2 (interior_mono inter_subset_right hint)

end PoincareConjecture.M76
