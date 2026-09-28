import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalNonexceptionalEndpointSphere
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalIntervalBundle
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutTrimContainment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalPrismTrimHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.NoL3EndpointComponent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalMarkedBoundaryExceptions
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PrismRawComponentHomology

set_option autoImplicit false
open Set Metric Geometry CategoryTheory Limits
namespace PoincareConjecture.M76.PrismBelt
universe u v
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 4000000 in
theorem original_nonexceptional_noL3_component_homology_retract
    {E : Type u} {X : Type v} {A ι κ ν : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    [Finite κ] [Finite ν] {e : ι → OpenPartialHomeomorph X V3} {R Qcut : Set X}
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgR : MapsTo g K.space R)
    (F : X → E) (hFc : Continuous F) (hFK : MapsTo F R K.space)
    (hFg : ∀ x ∈ K.space, F (g x) = x) (hgF : ∀ x ∈ R, g (F x) = x)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hmark : ∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ J.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (hSR : (⋃ i,S i) ⊆ interior R)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g (⋃ i,S i) s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (B : OriginalTetrahedralCutFamily K g (⋃ i,S i))
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball, B.DiskIndex j.1.1)
    (hne : ∀ j, i₀ j ≠ i₁ j)
    (hcap : ∀ j, B.cut j.1.1 (i₀ j) ⊆ B.boundary j.1.1 j.1.2 ∧
      B.cut j.1.1 (i₁ j) ⊆ B.boundary j.1.1 j.1.2)
    (H : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      (B.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ B.ball j.1.1 j.1.2)
    (hH : ∀ j, (H j).IsFinitePL)
    (hzero : ∀ j y, (H j y : E) ∈ B.cut j.1.1 (i₀ j) ↔ (y : E × ℝ).2 = 0)
    (hone : ∀ j y, (H j y : E) ∈ B.cut j.1.1 (i₁ j) ↔ (y : E × ℝ).2 = 1)
    (flip : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (B.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (B.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (C : ∀ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      (B.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hC : ∀ j, (C j).IsFinitePL)
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (B.cut j.1.1 (i₀ j)) x))
    (O N : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ N i)
    (hO : ∀ i, IsOpen (O i)) (hON : ∀ i, O i ⊆ N i)
    (hOR : ∀ i, O i ⊆ R) (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (bad : Set (ConnectedComponents (K.space \ g ⁻¹' ⋃ i,S i : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i,(D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ∀ hy : (y : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
        ConnectedComponents.mk (⟨y,hy⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∈ bad)
    (τ : (⋃ j,prismEnds (C j)) ≃ₜ (⋃ j,prismEnds (C j))) (hτ : Function.Involutive τ)
    (hτends : ∀ j (a : B.cut j.1.1 (i₀ j)) b,
      (τ (prismEndpointLift C j a b) : E) = prismEndMap (C j) a (!b))
    (p : (⋃ j,prismEnds (C j) : Set E))
    (hpbad : ∀ hp : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
      ConnectedComponents.mk (⟨p,hp⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad)
    (hpboundary : ∀ hp : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i,
      ConnectedComponents.mk (⟨p,hp⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉
        originalMarkedBoundaryComponents K J g (⋃ i,S i))
    (hQ : IsCompact Qcut) (hQPL : PLDomain e Qcut) (hQR : Qcut ⊆ R)
    (hQS : Disjoint Qcut (⋃ i,S i)) (hno : HasNoPuncturedSphereComponents e F Qcut)
    (Sb : ν → Set X) (sSb : ∀ i, ChartwisePLSphere e (Sb i))
    (hbdis : Pairwise fun i j => Disjoint (Sb i) (Sb j))
    (hfront : frontier Qcut = frontier R ∪ ⋃ i,Sb i)
    (x : X) (hx : x ∈ Qcut)
    (hxp : F x ∈ connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E))
    (Rmod : ModuleCat.{u} (ZMod 2)) [Nontrivial Rmod] :
    ∃ (i : Rmod ⟶ (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ j,prismTrim (H j)) (p : E)))).homology Rmod 1)
      (r : (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ j,prismTrim (H j)) (p : E)))).homology Rmod 1 ⟶ Rmod),
      i ≫ r = 𝟙 Rmod ∧ ¬ IsZero ((TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ j,prismTrim (H j)) (p : E)))).homology Rmod 1) ∧
      ∃ (i' : Rmod ⟶ (TopCat.toSSet.obj
          (TopCat.of (connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E)))).homology Rmod 1)
        (r' : (TopCat.toSSet.obj
          (TopCat.of (connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E)))).homology Rmod 1 ⟶ Rmod),
        i' ≫ r' = 𝟙 Rmod ∧ ¬ IsZero ((TopCat.toSSet.obj
          (TopCat.of (connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E)))).homology Rmod 1) := by
  classical
  let : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  let (t : K.FaceOfCard 4) : Finite (B.BallIndex t) := B.finite_ball t
  let : Finite (RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball) := by
    unfold RegularOriginalCutCell
    infer_instance
  have hgi : InjOn g K.space := by
    intro y hy z hz he
    exact (hFg y hy).symm.trans ((congrArg F he).trans (hFg z hz))
  obtain ⟨r,hr,hrv,_,P,hP,_,_⟩ := exists_original_nonexceptional_endpoint_sphere K hK hpure
    g hg.continuousOn hgR F hFc hFK hFg hgF hF S sS hdis D G hW hZ hL haffine B i₀ i₁
    hne hcap H hH hzero hone flip hformula C hC hCv O N W hO hON hOR hSO hcenter bad hbad p hpbad
  have hFQS : Disjoint (F '' Qcut) (g ⁻¹' ⋃ i,S i) := by
    apply disjoint_left.mpr
    rintro _ ⟨y,hy,rfl⟩ hs
    exact disjoint_left.mp hQS hy (by simpa only [mem_preimage,hgF y (hQR hy)] using hs)
  obtain ⟨δ,hδ,hhalf,hsmall,Cδ,hCδ,hCδv,havoidδ,_,hcomponents,_⟩ :=
    exists_original_compact_cut_trim K hK g hgi hpure D G hW hZ hL haffine B bad
      (fun s y hy => hbad s y hy _) i₀ i₁ hne hcap H hH hzero hone flip hformula
      (F '' Qcut) (hQ.image hFc) hFQS
  have havoid : Disjoint (⋃ j,prismTrim (H j)) (g ⁻¹' ⋃ i,S i) :=
    havoidδ.mono_left (iUnion_mono (fun j => prismTrim_subset_trimAt (H j) hsmall))
  obtain ⟨T,hT,_,_,hTcomponent⟩ := exists_original_prism_trim_homeomorph K hK g hgi D G
    hW hZ hL haffine B i₀ H flip hformula C hC hCv havoid δ hδ.le hhalf Cδ hCδ hCδv havoidδ
  obtain ⟨L,hLval,Wint,_,hWboundary,_⟩ := exists_original_prism_interval_bundle K hK g hgi
    D G hW hZ hL haffine B i₀ H flip hformula C hCv havoid τ hτ hτends
  have hpairs := original_trimmed_fiber_end_pairs_agree K g hgi D G hW hZ hL haffine
    B i₀ H flip hformula C hCv havoid
  have hpCut : (p : E) ∈ K.space \ g ⁻¹' ⋃ i,S i :=
    connectedComponentIn_nonempty_iff.mp ⟨F x,hxp⟩
  obtain ⟨_,_,hsub,hcontain,hlabel⟩ := hcomponents ⟨p,hpCut⟩ (hpbad hpCut)
  let ep := prismEndpointInclusion C p
  have hTpCut : (T ep : E) ∈ K.space \ g ⁻¹' ⋃ i,S i := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp (T ep).property
    exact ⟨K.convexHull_subset_space j.1.1.2.1 (B.ball_subset_tetrahedron j.1.1 j.1.2
      (prismTrimAt_subset (H j) δ hj)),fun hs => disjoint_left.mp havoidδ (T ep).property hs⟩
  have hTp : (T ep : E) ∈ connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E) :=
    (hTcomponent ep).subset (mem_connectedComponentIn hTpCut)
  have hTpUnion : (T ep : E) ∈ ⋃ j : OriginalComponentCutCell D B (p : E),
      prismTrimAt (H j.1) δ := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp (T ep).property
    exact mem_iUnion.mpr ⟨⟨j,⟨T ep,⟨prismTrimAt_subset (H j) δ hj,hTpCut.2⟩,hTp⟩⟩,hj⟩
  have hactual := hlabel (T ep) hTpUnion
  have hNraw : connectedComponentIn (⋃ j,prismTrimAt (H j) δ) (T ep : E) ⊆
      connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E) := hactual.subset.trans hsub
  have hrawcontain : connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E) ∩ F '' Qcut ⊆
      connectedComponentIn (⋃ j,prismTrimAt (H j) δ) (T ep : E) :=
    hcontain.trans hactual.symm.subset
  have hinterior := original_component_closure_mapsTo_interior_of_not_boundary_exception K J hK
    g (image_subset_iff.mpr hgR) hmark hSR ⟨p,hpCut⟩ (hpboundary hpCut)
  obtain ⟨i₀',r₀',hir₀,hne₀⟩ := endpoint_component_homology_retract_of_noL3 K g hg hgi F hF hFg hQ hQPL hno
    Sb sSb hbdis hfront C hC L hLval hpairs τ hτ hτends Wint hWboundary T hT p P hP
    (hNraw.trans ((connectedComponentIn_subset _ _).trans sdiff_subset))
    (fun _ hy => hinterior (subset_closure (hNraw hy))) hx
    (physical_cut_component_subset_of_raw_trim g F hFc hFK hgF hQR hQS (p : E)
      hrawcontain x hx hxp) Rmod
  obtain ⟨Wraw,hWraw,_⟩ := exists_original_raw_prism_core_homeomorph.{0} K hK g hgi D G
    hW hZ hL haffine B i₀ i₁ hne hcap H hzero hone flip hformula C hCv r hr.continuousOn hrv
  have hV : ((⋃ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
      B.ball j.1.1 j.1.2) \ g ⁻¹' ⋃ i,S i : Set E) ⊆ K.space \ g ⁻¹' ⋃ i,S i := by
    rintro y ⟨hy,hs⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact ⟨K.convexHull_subset_space j.1.1.2.1 (B.ball_subset_tetrahedron j.1.1 j.1.2 hj),hs⟩
  have htrim : (⋃ j,prismTrim (H j)) ⊆ K.space \ g ⁻¹' ⋃ i,S i := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact hV ⟨mem_iUnion.mpr ⟨j,prismTrim_subset (H j) hj⟩,
      fun hs => disjoint_left.mp havoid hy hs⟩
  have hcover : connectedComponentIn (K.space \ g ⁻¹' ⋃ i,S i) (p : E) ⊆
      (⋃ j : RegularOriginalCutCell K g (⋃ i,S i) D B.BallIndex B.ball,
        B.ball j.1.1 j.1.2) \ g ⁻¹' ⋃ i,S i := by
    intro y hy
    have hyCut := connectedComponentIn_subset _ _ hy
    have hclass := (Topology.mem_componentIn_iff_component_class hpCut hyCut).mp hy
    have hybad : ConnectedComponents.mk (⟨y,hyCut⟩ : (K.space \ g ⁻¹' ⋃ i,S i : Set E)) ∉ bad := by
      simpa only [hclass] using hpbad hpCut
    obtain ⟨j,hj⟩ := exists_regular_cell_of_component_not_mem_bad K g hgi hpure D B bad
      (fun s y hy => hbad s y hy _) ⟨y,hyCut⟩ hybad
    exact ⟨mem_iUnion.mpr ⟨j,hj⟩,hyCut.2⟩
  obtain ⟨i₁',r₁',hir₁⟩ := exists_raw_prism_component_homology_retract H C hCv L hLval r hrv
    Wraw hWraw htrim hV p hcover Rmod i₀' r₀' hir₀
  refine ⟨i₀',r₀',hir₀,hne₀,i₁',r₁',hir₁,?_⟩
  intro hzero
  have hi : i₁' = 0 := hzero.eq_of_tgt i₁' 0
  have hid : 𝟙 Rmod = 0 := hir₁.symm.trans (by rw [hi,zero_comp])
  have : Subsingleton Rmod := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero Rmod).mpr hid)
  exact false_of_nontrivial_of_subsingleton Rmod

end PoincareConjecture.M76.PrismBelt
