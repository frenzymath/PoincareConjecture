import PoincareConjecture.Proofs.M25.AppA_20_Fibration
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.NonseparatingCompactUnion
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ReturnOverlapGeometry
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ClosingThreePieces
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.CompactCutChart
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ClosingProductCharts
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ThreePieceCircleProjection
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicSmoothChainChart
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.LastSliceIsotopy
import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphIsotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25












theorem compactNonseparatingFibrationInput :
    CompactNonseparatingFibrationInput.{u} := by
  obtain ⟨ec, hcp, hccap, compactReturn⟩ :=
    NeckOnlyCover.exists_compact_whole_union_of_nonseparating.{u}
  obtain ⟨eg, hgp, _, geometry⟩ := NeckOnlyCover.exists_closing_return_geometry.{u}
  obtain ⟨ed, hdp, _, decompose⟩ :=
    BalancedNeckChain.exists_closing_three_piece_decomposition.{u}
  obtain ⟨ep, hpp, _, products⟩ := BalancedNeckChain.exists_closing_product_charts.{u}
  obtain ⟨ei, hip, _, lastSlice⟩ :=
    BalancedNeckChain.exists_central_sphere_isotopies_to_last_slice.{u}
  refine ⟨min ec (min eg (min ed (min ep ei))), by positivity,
    (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall hwhole hnon hcompact
  classical
  rcases le_min_iff.mp hsmall with ⟨hec, hsmall⟩
  rcases le_min_iff.mp hsmall with ⟨heg, hsmall⟩
  rcases le_min_iff.mp hsmall with ⟨hed, hsmall⟩
  rcases le_min_iff.mp hsmall with ⟨hep, hei⟩
  have hconnected : IsConnected (univ : Set M) := hwhole ▸ H.connected_X
  let : ConnectedSpace M := connectedSpace_iff_univ.mpr hconnected
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  obtain ⟨x0, hx0⟩ := H.connected_X.nonempty
  obtain ⟨N0, hN0, _hN0center⟩ := H.pointwise_center_cover x0 hx0
  obtain ⟨b, C, R, _Pold, _Qold, hshape, _hsource, hstart, _hquarters,
    _hhistory, _hincidence, _hRsource, heR, _hRfrontier, hRout, hRpositive,
    hreturn, _hPold, _hQold, _heQold, _hQoldcenter, _hwholeOld, _hcompactOld⟩ :=
    compactReturn H hec hwhole N0 hN0 (hnon N0 hN0)
  let L : ℝ := H.epsilon⁻¹
  let N := C.neck 0
  let B := C.neck (b : ℤ)
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  have hreturn' : ∀ c ∈ Ioo (-L) 0, ¬ Disjoint R.carrier (N.region (-L) c) := by
    simpa only [N, hstart] using hreturn
  obtain ⟨_P, Q, Rh, f, hN, hR, _lo, _rlo, _rhi, _hP, _hQP, hRh,
    heQ, heRh, _hQcenter, hf, bf, gSp, hhN, bN, gSm, hhR, bR, gS2,
    bandN, bandR, _hgeometryRest⟩ :=
    geometry H heg hwhole C 0 (b : ℤ) hshape R heR hRpositive hRout hreturn'
  let Sm : Set M := range (fun q => N.coordinate_map (q, hN q))
  let Sp : Set M := range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4))
  let Gminus : Set M := N.coordinate_map '' {z | -L < z.2 ∧ z.2 < hN z.1}
  let Pplus : Set M := connectedComponentIn (U \ Sp)
    (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
  let K : Set M := U \ (Gminus ∪ Pplus)
  let DR : Set M := Rh.coordinate_map '' {z | f z.1 < z.2 ∧ z.2 < hR z.1}
  let DQ : Set M := Q.region (-L / 4) 0
  let W : Set M := (U ∪ R.carrier) ∪ Q.carrier
  obtain ⟨hKcompact, _hKfrontier, _hDRopen, _hDRconnected, _hDQopen,
    _hDQconnected, hclDR, hclDQ, hDRcompact, hDQcompact, _hDRfrontier,
    _hDQfrontier, hKR, hKQ, hRQ, hpieces, _hpiecesRest⟩ :=
    decompose C hed 0 (b : ℤ) hshape R Rh Q heR hRh heQ hRpositive hRout
      f hN hR hf.continuous hhN.continuous hhR.continuous bf bN bR
      gSp gSm gS2 bandN bandR
  change (K ∪ closure DR) ∪ closure DQ = W at hpieces
  have hWcompact : IsCompact W := by
    rw [← hpieces]
    exact (hKcompact.union hDRcompact).union hDQcompact
  have hWopen : IsOpen W :=
    ((isOpen_iUnion fun i => isOpen_iUnion fun _ =>
      (C.neck i).carrier_open).union R.carrier_open).union Q.carrier_open
  have h0active : (0 : ℤ) ∈ C.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, by positivity⟩
  have hWwhole : W = univ :=
    IsClopen.eq_univ ⟨hWcompact.isClosed, hWopen⟩
      ⟨N.center, Or.inl (Or.inl (mem_iUnion₂.mpr
        ⟨0, h0active, N.central_sphere_subset N.center_on_central_sphere⟩))⟩
  obtain ⟨eta, heta, _hetacap, e, hsource, hsmooth, himage0, himage1raw,
    himage2raw, hlower0, hlower1, hlower2, hboundary⟩ :=
    products C hshape hep Rh Q heRh heQ f hN hR hf hhN hhR bf bN bR gSp gSm gS2
  change e 0 '' (univ ×ˢ Icc (0 : ℝ) 1) = K at himage0
  have himage1 : e 1 '' (univ ×ˢ Icc (0 : ℝ) 1) = closure DR :=
    himage1raw.trans hclDR.symm
  have himage2 : e 2 '' (univ ×ˢ Icc (0 : ℝ) 1) = closure DQ :=
    himage2raw.trans hclDQ.symm
  have hinter (i : Fin 3) :
      (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)) := by
    fin_cases i
    · change (e 0 '' _) ∩ (e 1 '' _) = range (fun q : UnitTwoSphere => e 1 (q, 0))
      rw [himage0, himage1, hlower1]
      exact hKR
    · change (e 1 '' _) ∩ (e 2 '' _) = range (fun q : UnitTwoSphere => e 2 (q, 0))
      rw [himage1, himage2, hlower2]
      exact hRQ
    · change (e 2 '' _) ∩ (e 0 '' _) = range (fun q : UnitTwoSphere => e 0 (q, 0))
      rw [himage2, himage0, hlower0, inter_comm]
      exact hKQ
  have hthree : (⋃ i : Fin 3, e i '' (univ ×ˢ Icc (0 : ℝ) 1)) =
      (K ∪ closure DR) ∪ closure DQ := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (Or.inl (himage0 ▸ hi))
      · exact Or.inl (Or.inr (himage1 ▸ hi))
      · exact Or.inr (himage2 ▸ hi)
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion.mpr ⟨0, himage0.symm ▸ hx⟩
      · exact mem_iUnion.mpr ⟨1, himage1.symm ▸ hx⟩
      · exact mem_iUnion.mpr ⟨2, himage2.symm ▸ hx⟩
  obtain ⟨p, hpcont, hpsurj, hpsmooth, hcharts, hseams⟩ :=
    exists_circle_projection_of_three_product_charts heta e hsource hsmooth
      hboundary hinter (hthree.trans (hpieces.trans hWwhole))
  let necks : Set (EpsilonNeck g) := (C.neck '' C.shape.active) ∪ {Rh, Q}
  have hnecks (A : EpsilonNeck g) (hA : A ∈ necks) : A.epsilon = H.epsilon := by
    rcases hA with ⟨i, hi, rfl⟩ | hA
    · exact C.epsilon_eq i hi
    · rcases mem_insert_iff.mp hA with rfl | hA
      · exact heRh
      · obtain rfl := mem_singleton_iff.mp hA
        exact heQ
  have hRhcarrier : Rh.carrier = R.carrier := by
    rcases hRh with rfl | rfl <;> rfl
  have hneckCover : (univ : Set M) = ⋃ A : {A // A ∈ necks}, A.1.carrier := by
    apply Subset.antisymm
    · intro x hx
      have hxW : x ∈ W := hWwhole.symm ▸ hx
      rcases hxW with (hxU | hxR) | hxQ
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
        exact mem_iUnion.mpr ⟨⟨C.neck i, Or.inl ⟨i, hi, rfl⟩⟩, hxi⟩
      · exact mem_iUnion.mpr ⟨⟨Rh, Or.inr (mem_insert _ _)⟩, hRhcarrier.symm ▸ hxR⟩
      · exact mem_iUnion.mpr ⟨⟨Q, Or.inr (mem_insert_of_mem _ (mem_singleton _))⟩, hxQ⟩
    · exact subset_univ _
  have enlarge {V S T : Set M} (h : SmoothSphereIsotopicIn V S T) :
      SmoothSphereIsotopicIn univ S T := by
    obtain ⟨F, hF, ht, hstart, hend⟩ := h
    exact ⟨F, hF, fun t ht' => ⟨(ht t ht').1, subset_univ _⟩, hstart, hend⟩
  have hRhSp : SmoothSphereIsotopicIn Rh.carrier Rh.central_sphere Sp := by
    have hzero (_q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-Rh.epsilon⁻¹) Rh.epsilon⁻¹ :=
      Rh.zero_mem_interval
    have hfdomain (q : UnitTwoSphere) : f q ∈ Ioo (-Rh.epsilon⁻¹) Rh.epsilon⁻¹ := by
      rw [heRh]
      change f q ∈ Ioo (-L) L
      constructor <;> linarith [(bf q).1, (bf q).2]
    have h := Rh.m25_coordinate_graphs_isotopic (fun _ => 0) f
      contMDiff_const hf hzero hfdomain
    rw [Rh.coordinate_zero_range, ← gSp] at h
    exact h
  have hQSm : Q.central_sphere = Sm := (gSm.trans Q.coordinate_zero_range).symm
  have hfiber0 : {x : M | x ∈ univ ∧ p x = Topology3D.periodCircleParam 3 0} = Sm := by
    have h := (hseams 0).trans hlower0
    simpa only [mem_univ, true_and, preimage, mem_singleton_iff,
      Fin.val_zero, Nat.cast_zero] using h
  have hfiber1 : {x : M | x ∈ univ ∧ p x = Topology3D.periodCircleParam 3 1} = Sp := by
    have h := (hseams 1).trans hlower1
    simpa only [mem_univ, true_and, preimage, mem_singleton_iff,
      Fin.val_one, Nat.cast_one] using h
  have hisotopy (A : EpsilonNeck g) (hA : A ∈ necks) : ∃ z : UnitCircle,
      SmoothSphereIsotopicIn univ A.central_sphere {x | x ∈ univ ∧ p x = z} := by
    rcases hA with ⟨i, hi, rfl⟩ | hA
    · refine ⟨Topology3D.periodCircleParam 3 1, ?_⟩
      rw [hfiber1]
      exact enlarge (lastSlice C hshape hei i hi)
    · rcases mem_insert_iff.mp hA with rfl | hA
      · refine ⟨Topology3D.periodCircleParam 3 1, ?_⟩
        rw [hfiber1]
        exact enlarge hRhSp
      · have heq := mem_singleton_iff.mp hA
        subst A
        refine ⟨Topology3D.periodCircleParam 3 0, ?_⟩
        rw [hfiber0, ← hQSm]
        exact enlarge Q.m25_central_sphere_isotopic_self
  let model : SphereBundleCircleModel.{u} := {
    carrier := M
    carrier_topology := inferInstance
    carrier_charted := inferInstance
    carrier_manifold := inferInstance
    projection := p
    projection_continuous := hpcont
    projection_surjective := hpsurj
    projection_smooth := hpsmooth
    local_trivialization := by
      intro z
      obtain ⟨V, hV, hz, T, hTs, hTt, hTsm, hTism, hTp⟩ := hcharts z
      refine ⟨V, hV, hz, T, T.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hTs, ← hTt]
        exact T.image_source_eq_target
      · rw [← hTs]
        exact T.leftInvOn
      · rw [← hTt]
        exact T.rightInvOn
      · rwa [← hTs]
      · rwa [← hTt]
      · rwa [← hTs] }
  refine ⟨{
    epsilon := H.epsilon
    epsilon_pos := H.epsilon_pos
    epsilon_le_one_two_hundred := hec.trans hccap
    carrier := univ
    contains_X := subset_univ _
    connected := hconnected
    compact := hcompact
    component := ⟨N0.center, (PreconnectedSpace.connectedComponent_eq_univ N0.center).symm⟩
    model := model
    homeomorph := Homeomorph.Set.univ M
    forward := id
    inverse := id
    forward_eq := fun _ => rfl
    inverse_eq := fun _ => rfl
    forward_smooth := contMDiff_id.contMDiffOn
    inverse_smooth := contMDiff_id
    necks := necks
    neck_epsilon := hnecks
    neck_cover := hneckCover
    fiber_isotopy := hisotopy }, rfl, rfl⟩

end PoincareConjecture.M25
