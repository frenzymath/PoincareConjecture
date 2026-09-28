import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.EssentialAnnulusBallProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedMeridianSphereObstruction









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Cube" => Set.prod Square (Icc (-1 : ℝ) 1)

theorem no_essential_compression_disk_in_original_model
    {ι κ α E W : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (K : SimplicialComplex ℝ E) (F : LatticeHandleAmbient ι κ L → E)
    (H : latticeHandleDomain ι κ L ≃ₜ K.space) (g : E → latticeHandleDomain ι κ L)
    (hKs : K.space = F '' latticeHandleDomain ι κ L)
    (hH : ∀ x, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : LatticeHandleAmbient ι κ L) =
      (H.symm z : LatticeHandleAmbient ι κ L))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space)
    (hball : IsFinitePLBallPair V3 (F '' D) (F '' frontier D))
    (J B : Set E) (d r : Bool → Set E)
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) (r i))
    (hdS : ∀ i, d i ⊆ F '' frontier D) (hdis : Disjoint (d false) (d true))
    (hcover : d false ∪ d true = J) (hrcover : r false ∪ r true = B)
    (hJmark : J = F '' (D ∩ frontier (latticeHandleDomain ι κ L)))
    (ann : Ann ≃ₜ (F '' frontier D \ (J \ B) : Set E)) (hann : ann.IsFinitePL)
    (hlo : ∀ z : Ann, depth 8 (z : P2) = -1 ↔ (ann z : E) ∈ r false)
    (hhi : ∀ z : Ann, depth 8 (z : P2) = 1 ↔ (ann z : E) ∈ r true)
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (a : V2 → P2) (ha : FinitePiecewiseAffineOn a Q2)
    (haval : ∀ x : Q2, a x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1)
    {c q : Set W} (hc : IsFinitePLBallPair P2 c q)
    (f : W → LatticeHandleAmbient ι κ L) (hf : PolyhedralPLInCharts e f c)
    (hfi : InjOn f c) (hfR : f '' c ⊆ interior (latticeHandleDomain ι κ L))
    (hfD : (f '' c) ∩ D = f '' q)
    (hfrim : F '' (f '' q) = (fun z : Ann => (ann z : E)) '' range gamma) : False := by
  obtain ⟨Q, hQ, hends, hfront, hcurve⟩ :=
    exists_cube_product_with_prescribed_disks_and_essential_meridian hball d r hd hdS hdis
      hcover hrcover ann hann hlo hhi gamma hinj a ha haval hdepth hessential
  obtain ⟨p, G, hp, hval, hpi, himage, hmem⟩ := exists_original_cube_transport
    b.subset_domain K F H g hKs hH hg hgPL Q hQ
  have hpD (z : P3) (hz : z ∈ Cube) : p z ∈ D := himage.subset ⟨z, hz, rfl⟩
  have hboundary (z : P3) (hz : z ∈ Cube) : p z ∈ frontier D ↔ z ∈ frontier Cube :=
    (hmem _ (b.ball.boundary_subset.trans b.subset_domain) ⟨z, hz⟩).trans (hfront ⟨z, hz⟩)
  have hRboundary (z : P3) (hz : z ∈ Cube) :
      p z ∈ frontier (latticeHandleDomain ι κ L) ↔ |z.2| = 1 := by
    have hm : p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        p z ∈ D ∩ frontier (latticeHandleDomain ι κ L) :=
      ⟨fun h => ⟨hpD z hz, h⟩, And.right⟩
    rw [hm, hmem _ (inter_subset_left.trans b.subset_domain) ⟨z, hz⟩,
      ← hJmark, ← hcover, mem_union, hends, hends]
    simp only [Bool.false_eq_true, if_false, if_true, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    exact or_comm
  have hend (side : Bool) : p ((0, 0), if side then 1 else -1) ∈
      frontier (latticeHandleDomain ι κ L) := by
    have hz : ((0, 0), if side then (1 : ℝ) else -1) ∈ Cube := by
      change ((-1 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ (-1 ≤ (0 : ℝ) ∧ 0 ≤ 1)) ∧
        (-1 ≤ (if side then (1 : ℝ) else -1) ∧ (if side then (1 : ℝ) else -1) ≤ 1)
      cases side <;> norm_num
    apply (hRboundary _ hz).mpr
    cases side <;> norm_num
  have hmeridian : p '' (Square ×ˢ {(0 : ℝ)}) ⊆
      interior (latticeHandleDomain ι κ L) := by
    rintro x ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    have hzc : z ∈ Cube := ⟨hz.1, by rw [hz0]; norm_num⟩
    rw [← self_sdiff_frontier]
    refine ⟨b.subset_domain (hpD z hzc), ?_⟩
    intro h
    have hh := (hRboundary z hzc).mp h
    norm_num [hz0] at hh
  have hsq (z : Square) : (z : P2) ∈ frontier Square ↔
      |z.val.1| = 1 ∨ |z.val.2| = 1 := by
    change (z : P2) ∈ frontier (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ↔ _
    rw [frontier_prod_eq]
    simp only [isClosed_Icc.closure_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1),
      mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, z.property.1, z.property.2,
      true_and, and_true, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    tauto
  have hrR : f '' q ⊆ latticeHandleDomain ι κ L :=
    (image_mono hc.1).trans (hfR.trans interior_subset)
  have hcontact (z : P3) (hz : z ∈ Cube) :
      p z ∈ f '' q ↔ z ∈ frontier Square ×ˢ {(0 : ℝ)} := by
    rw [hmem _ hrR ⟨z, hz⟩, hfrim, hcurve]
    exact and_congr (hsq ⟨z.1, hz.1⟩).symm Iff.rfl
  have hrim : f '' q = p '' (frontier Square ×ˢ {(0 : ℝ)}) := by
    apply Subset.antisymm
    · intro x hx
      have hxD : x ∈ D := (hfD.symm.subset hx).2
      obtain ⟨z, hz, rfl⟩ := himage.symm.subset hxD
      exact ⟨z, (hcontact z hz).mp hx, rfl⟩
    · rintro x ⟨z, hz, rfl⟩
      have hzs : z.1 ∈ Square := (isClosed_Icc.prod isClosed_Icc).frontier_subset hz.1
      have hzc : z ∈ Cube := ⟨hzs, by rw [show z.2 = 0 from hz.2]; norm_num⟩
      exact (hcontact z hzc).mpr hz
  exact no_standard_meridian_compression_disk L he hdim p hp hpi himage hboundary
    hend hmeridian hc f hf hfi hfR hrim (hfD.trans hrim)



theorem HamiltonMarkedProtectedBall.exists_original_annulus_noncompression
    {ι κ α W : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (J B : SimplicialComplex ℝ (s → ℝ × V3))
      (ann : Ann ≃ₜ (F '' frontier D \ (J.space \ B.space) : Set (s → ℝ × V3))),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F (latticeHandleDomain ι κ L) ∧ J.faces.Finite ∧ B.faces.Finite ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      B.space = F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ∧
      ann.IsFinitePL ∧
      ∀ (gamma : C(Q2, Ann)), Function.Injective gamma →
        ∀ a : V2 → P2, FinitePiecewiseAffineOn a Q2 →
          (∀ x : Q2, a x = (gamma x : P2)) →
          (∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1) →
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 →
          ∀ (c q : Set W), IsFinitePLBallPair P2 c q →
            ∀ f : W → LatticeHandleAmbient ι κ L, PolyhedralPLInCharts e f c → InjOn f c →
              f '' c ⊆ interior (latticeHandleDomain ι κ L) →
              (f '' c) ∩ D = f '' q →
              F '' (f '' q) = (fun z : Ann => (ann z : s → ℝ × V3)) '' range gamma → False := by
  classical
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  obtain ⟨s, F, K, J, B, H, g, d, r, ann, C, hFc, hF, hfi, hK, hKs, hH, hgc, hg,
      hgPL, hball, hJK, hBJ, hJ, hB, hJmark, hBmark, hd, hdis, hcover, hrcover,
      hann, hlo, hhi, _⟩ := b.exists_original_disk_complement_model he (by omega)
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hm⟩
    · omega
    · exact hm
  have hattachS : hamiltonAttachingBlock ι κ L (3 / 2) ⊆ frontier D := by
    rw [← hmark]
    intro x hx
    exact ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset hx).1
  have hdS (i : Bool) : d i ⊆ F '' frontier D := by
    intro x hx
    apply image_mono hattachS
    apply hcover.subset
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  refine ⟨s, F, J, B, ann, hFc, hF, hfi, hJ, hB, hJmark, hBmark, hann, ?_⟩
  intro gamma hinj a ha haval hdepth hessential c q hc f hf hfinj hfR hfD hfrim
  exact no_essential_compression_disk_in_original_model b he hdim K F H g hKs hH hg hgPL
    hball J.space B.space d r (fun i => (hd i).1) hdS hdis
    (hcover.trans hJmark.symm) hrcover
    (hJmark.trans (congrArg (fun U => F '' U) hmark.symm))
    ann hann hlo hhi gamma hinj a ha haval hdepth hessential hc f hf hfinj hfR hfD hfrim

end PoincareConjecture.M76
