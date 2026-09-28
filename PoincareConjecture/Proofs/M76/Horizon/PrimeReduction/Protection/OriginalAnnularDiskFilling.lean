import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.NullBoundaryDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalEssentialCompression
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "V3" => (Fin 3 → ℝ)

theorem standard_annulus_lower_rim_not_nullhomotopic :
    ¬ (planarAnnulusRim (ContinuousMap.id Ann) false).Nullhomotopic := by
  intro hnull
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let radial : C(Ann, Circle) :=
    ⟨fun z => (Dehn.annulusCylinderHomeomorph.symm z).2,
      continuous_snd.comp Dehn.annulusCylinderHomeomorph.symm.continuous⟩
  have hcomp : radial.comp (planarAnnulusRim (ContinuousMap.id Ann) false) =
      ContinuousMap.id Circle := by
    ext z
    change (Dehn.annulusCylinderHomeomorph.symm (Dehn.annulusRimPoint false z)).2 = z
    rw [← Dehn.annulusCylinderHomeomorph_zero, Dehn.annulusCylinderHomeomorph.symm_apply_apply]
  have hid : (ContinuousMap.id Circle).Nullhomotopic := hcomp ▸ hnull.comp_right radial
  let : ContractibleSpace Circle := (contractible_iff_id_nullhomotopic Circle).mpr hid
  exact AddCircle.periodLoop_not_homotopic_refl (4 * (8 : ℝ))
    (SimplyConnectedSpace.paths_homotopic _ _)

theorem exists_finitePL_disk_of_null_annular_circle
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (a : V2 → P2) (ha : FinitePiecewiseAffineOn a Q2)
    (haval : ∀ x : Q2, a x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hnull : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) = 1) :
    ∃ d : Set P2, IsFinitePLBallPair P2 d (range (fun x : Q2 => (gamma x : P2))) ∧
      d ⊆ {z : P2 | -1 < depth 8 z ∧ depth 8 z < 1} := by
  let ambient : C(Q2, P2) := ⟨fun x => gamma x, continuous_subtype_val.comp gamma.continuous⟩
  have hamb : Function.Injective ambient := fun x y h => hinj (Subtype.ext h)
  obtain ⟨n, P, hP, hi, hPb⟩ :=
    Dehn.exists_polygon_of_finitePL_embedded_square_rim ambient hamb a ha haval
  have hboundary (x : P2) (hx : x ∈ P.boundary ℝ) : -1 < depth 8 x ∧ depth 8 x < 1 := by
    obtain ⟨z, rfl⟩ := hPb.subset hx
    exact hdepth z
  let boundary : C(P.boundary ℝ, Ann) := ⟨fun x =>
    ⟨x, mem_squareAnnulus_iff_depth.mpr
      ⟨(hboundary x x.property).1.le, (hboundary x x.property).2.le⟩⟩,
      continuous_subtype_val.subtype_mk _⟩
  let f : Q2 → P.boundary ℝ := fun x => ⟨gamma x, hPb.symm.subset (mem_range_self x)⟩
  have hfc : Continuous f := ambient.continuous.subtype_mk _
  have hfi : Function.Injective f := fun x y h => hinj
    (Subtype.ext (congrArg (fun z : P.boundary ℝ => (z : P2)) h))
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨z, hz⟩ := hPb.subset x.property
    exact ⟨z, Subtype.ext hz⟩
  let H : Q2 ≃ₜ P.boundary ℝ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩) hfc
  have hgammaNull := Dehn.nullhomotopic_of_squareRimLoop gamma (Path.Homotopic.Quotient.eq.mp hnull)
  have heq : gamma.comp ⟨H.symm, H.symm.continuous⟩ = boundary := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change (gamma (H.symm x) : P2) = (x : P2)
    exact congrArg Subtype.val (H.apply_symm_apply x)
  have hbNull : boundary.Nullhomotopic := heq ▸ hgammaNull.comp_left ⟨H.symm, H.symm.continuous⟩
  obtain ⟨hd, hinside⟩ := Dehn.Annuli.polygon_disk_in_essential_annulus_of_null_boundary
    (ContinuousMap.id Ann) standard_annulus_lower_rim_not_nullhomotopic
    P hP hi hboundary boundary (fun _ => rfl) hbNull
  exact ⟨closure P.inside, hPb ▸ hd, hinside⟩

theorem exists_finitePL_disk_in_annulus_of_null_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} (H : Ann ≃ₜ A) (hH : H.IsFinitePL)
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (a : V2 → P2) (ha : FinitePiecewiseAffineOn a Q2)
    (haval : ∀ x : Q2, a x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hnull : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) = 1) :
    ∃ d : Set E, IsFinitePLBallPair P2 d ((fun z : Ann => (H z : E)) '' range gamma) ∧
      d ⊆ (fun z : Ann => (H z : E)) ''
        {z : Ann | -1 < depth 8 (z : P2) ∧ depth 8 (z : P2) < 1} := by
  obtain ⟨d, hd, hdopen⟩ := exists_finitePL_disk_of_null_annular_circle
    gamma hinj a ha haval hdepth hnull
  obtain ⟨f, hf, hfval⟩ := hH
  have hfi : InjOn f Ann := by
    intro x hx y hy h
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hfval ⟨x, hx⟩).trans (h.trans (hfval ⟨y, hy⟩).symm))))
  have hdAnn : d ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hdopen hz).1.le, (hdopen hz).2.le⟩
  have hbd : f '' range (fun x : Q2 => (gamma x : P2)) =
      (fun z : Ann => (H z : E)) '' range gamma := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨gamma z, mem_range_self z, hfval (gamma z)⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨gamma z, mem_range_self z, (hfval (gamma z)).symm⟩
  refine ⟨f '' d, hbd ▸ hd.image_of_subset hf hdAnn hfi, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  exact ⟨⟨z, hdAnn hz⟩, hdopen hz, hfval ⟨z, hdAnn hz⟩⟩

theorem HamiltonMarkedProtectedBall.exists_original_annular_disk_filling
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
          ∀ (c q : Set W), IsFinitePLBallPair P2 c q →
            ∀ f : W → LatticeHandleAmbient ι κ L, PolyhedralPLInCharts e f c → InjOn f c →
              f '' c ⊆ interior (latticeHandleDomain ι κ L) →
              (f '' c) ∩ D = f '' q →
              F '' (f '' q) = (fun z : Ann => (ann z : s → ℝ × V3)) '' range gamma →
              ∃ (d : Set (s → ℝ × V3)) (j : (s → ℝ × V3) → LatticeHandleAmbient ι κ L),
                IsFinitePLBallPair P2 d (F '' (f '' q)) ∧
                d ⊆ F '' frontier D \ J.space ∧ PolyhedralPLInCharts e j d ∧
                InjOn j d ∧ j '' d ⊆ frontier D ∩ interior (latticeHandleDomain ι κ L) ∧
                j '' (F '' (f '' q)) = f '' q := by
  classical
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  obtain ⟨s, F, K, J, B, H, g, dc, r, ann, C, hFc, hF, hfi, hK, hKs, hH, hgc, hg,
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
  have hdS (i : Bool) : dc i ⊆ F '' frontier D := by
    intro x hx
    apply image_mono hattachS
    apply hcover.subset
    cases i
    · exact Or.inl hx
    · exact Or.inr hx
  refine ⟨s, F, J, B, ann, hFc, hF, hfi, hJ, hB, hJmark, hBmark, hann, ?_⟩
  intro gamma hinj a ha haval hdepth c q hc f hf hfinj hfR hfD hfrim
  have hnull : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) = 1 := by
    by_contra hessential
    exact no_essential_compression_disk_in_original_model b he hdim K F H g hKs hH hg hgPL
      hball J.space B.space dc r (fun i => (hd i).1) hdS hdis
      (hcover.trans hJmark.symm) hrcover
      (hJmark.trans (congrArg (fun U => F '' U) hmark.symm))
      ann hann hlo hhi gamma hinj a ha haval hdepth hessential hc f hf hfinj hfR hfD hfrim
  obtain ⟨d, hdfill, hdinside⟩ := exists_finitePL_disk_in_annulus_of_null_circle
    ann hann gamma hinj a ha haval hdepth hnull
  have hdregion : d ⊆ F '' frontier D \ J.space := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hdinside hx
    refine ⟨(ann z).property.1, ?_⟩
    intro hzJ
    have hzB : (ann z : s → ℝ × V3) ∈ B.space := by
      by_contra hn
      exact (ann z).property.2 ⟨hzJ, hn⟩
    rcases hrcover.symm.subset hzB with hloz | hhiz
    · have ht := (hlo z).mpr hloz
      linarith [hz.1]
    · have ht := (hhi z).mpr hhiz
      linarith [hz.2]
  have hdK : d ⊆ K.space := by
    rw [hKs]
    exact (hdregion.trans sdiff_subset).trans
      (image_mono (b.ball.boundary_subset.trans b.subset_domain))
  let j : (s → ℝ × V3) → LatticeHandleAmbient ι κ L := fun z => g z
  have hj : PolyhedralPLInCharts e j d := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨T, hT, hTs, _⟩, _⟩, _⟩ := hdfill
    rw [← hTs]
    exact hgPL.restrict_finite T hT (hTs.subset.trans hdK)
  have hFg (z : s → ℝ × V3) (hz : z ∈ K.space) : F (j z) = z := by
    change F (g z) = z
    rw [hg ⟨z, hz⟩, ← hH (H.symm ⟨z, hz⟩), H.apply_symm_apply]
  have hjimage : j '' d ⊆ frontier D ∩ interior (latticeHandleDomain ι κ L) := by
    rintro x ⟨z, hz, rfl⟩
    have hzfront : j z ∈ frontier D :=
      (original_model_mem_image_iff H F g hH hg
        (b.ball.boundary_subset.trans b.subset_domain) ⟨z, hdK hz⟩).mpr (hdregion hz).1
    refine ⟨hzfront, ?_⟩
    rw [← self_sdiff_frontier]
    refine ⟨(g z).property, ?_⟩
    intro hzold
    apply (hdregion hz).2
    rw [hJmark, ← hmark, ← hFg z (hdK hz)]
    exact ⟨j z, ⟨b.ball.boundary_subset hzfront, hzold⟩, rfl⟩
  have hgf (x : LatticeHandleAmbient ι κ L) (hx : x ∈ latticeHandleDomain ι κ L) :
      j (F x) = x := by
    apply hfi (g (F x)).property hx
    exact hFg (F x) (hKs.symm.subset ⟨x, hx, rfl⟩)
  refine ⟨d, j, hfrim.symm ▸ hdfill, hdregion, hj, ?_, hjimage, ?_⟩
  · intro x hx y hy h
    rw [← hFg x (hdK hx), ← hFg y (hdK hy)]
    exact congrArg F h
  · apply Subset.antisymm
    · rintro x ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [hgf y (interior_subset (hfR (image_mono hc.1 hy)))]
      exact hy
    · intro x hx
      exact ⟨F x, ⟨x, hx, rfl⟩, hgf x (interior_subset (hfR (image_mono hc.1 hx)))⟩

end PoincareConjecture.M76
