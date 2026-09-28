import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalNegativeReturnGeometry
import PoincareConjecture.Proofs.M25.AppA_21_Local.ShiftedClosingThreePieces
import PoincareConjecture.Proofs.M25.AppA_21_Local.ShiftedClosingProductCharts
import PoincareConjecture.Proofs.M25.AppA_21_Local.ClopenThreePieceProjection
import PoincareConjecture.Proofs.M25.AppA_21_Local.ClopenCircleCertificate
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.LastSliceIsotopy
import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphIsotopy

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture

theorem NeckOnlyCover.exists_circle_certificate_of_local_negative_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (C : BalancedNeckChain g H.epsilon),
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := H.epsilon⁻¹
        let N := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∀ (R : EpsilonNeck g), R.epsilon = H.epsilon →
          R.center ∈ closure (B.region 0 L) → R.center ∉ U →
          (∀ t ∈ Set.Ioo (-L) 0,
            ¬ Disjoint R.carrier (N.region (-L) t)) →
          ∀ (P : EpsilonNeck g), P ∈ H.necks →
            P.center ∈ H.X ∩ N.region (-L) (-(4 * L / 5)) →
            ∃ (Q : EpsilonNeck g) (F : SphereBundleCircleCertificate g H.X),
              (Q = P ∨ Q = P.reverse) ∧ F.epsilon = H.epsilon ∧
                F.carrier = (U ∪ R.carrier) ∪ Q.carrier := by
  obtain ⟨eg, hgp, hgcap, geometry⟩ :=
    NeckOnlyCover.exists_local_negative_return_geometry.{u}
  obtain ⟨ed, hdp, _, decompose⟩ :=
    BalancedNeckChain.exists_shifted_closing_three_piece_decomposition.{u}
  obtain ⟨ep, hpp, _, products⟩ :=
    BalancedNeckChain.exists_shifted_closing_product_charts.{u}
  obtain ⟨ei, hip, _, lastSlice⟩ :=
    BalancedNeckChain.exists_central_sphere_isotopies_to_last_slice.{u}
  refine ⟨min eg (min ed (min ep ei)), by positivity,
    (min_le_left _ _).trans hgcap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall C a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  rcases le_min_iff.mp hsmall with ⟨heg, hsmall⟩
  rcases le_min_iff.mp hsmall with ⟨hed, hsmall⟩
  rcases le_min_iff.mp hsmall with ⟨hep, hei⟩
  let L : ℝ := H.epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro R heR hy hout hreturn P hP hz
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  let v := (N.coordinate_inverse P.center).2
  let c := -(17 * L / 20) - v
  have hv : -L < v ∧ v < -(4 * L / 5) := hz.2.2
  have hshift : c ∈ Ioo (-L / 20) (3 * L / 20) := by
    dsimp only [c]
    constructor <;> linarith only [hv.1, hv.2]
  obtain ⟨Q, Rh, _w, f, hN, hR, _lo, _rlo, _rhi, hQP, hRh,
    heQ, heRh, _hw, _hu, _hv0, _hclose, _hcrossR, _hcrossQ,
    hf, bf, gSp, hhN, bN, gSm, hhR, bR, gS2, bandN, bandR,
    _hlo, _hloa, _hrlo, _hrmid, _hrhi, _hretained, hWcompact, hcomponent, hX⟩ :=
    geometry H heg C a b hshape R heR hy hout hreturn P hP hz
  let Sm : Set M := range (fun q => N.coordinate_map (q, hN q))
  let Sp : Set M := range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4))
  let Gminus : Set M := N.coordinate_map '' {z | -L < z.2 ∧ z.2 < hN z.1}
  let Pplus : Set M := connectedComponentIn (U \ Sp)
    (B.coordinate_map ((B.coordinate_inverse B.center).1, 7 * L / 8))
  let K : Set M := U \ (Gminus ∪ Pplus)
  let DR : Set M := Rh.coordinate_map '' {z | f z.1 < z.2 ∧ z.2 < hR z.1}
  let DQ : Set M := Q.region (c - L / 4) c
  let W : Set M := (U ∪ R.carrier) ∪ Q.carrier
  change IsCompact W at hWcompact
  change W = connectedComponent P.center at hcomponent
  change H.X ⊆ W at hX
  have hWconnected : IsConnected W := by
    rw [hcomponent]
    exact isConnected_connectedComponent
  have hWopen : IsOpen W :=
    ((isOpen_iUnion fun i => isOpen_iUnion fun _ =>
      (C.neck i).carrier_open).union R.carrier_open).union Q.carrier_open
  let Wo : TopologicalSpace.Opens M := ⟨W, hWopen⟩
  obtain ⟨_hKcompact, _hKfrontier, _hDRopen, _hDRconnected, _hDQopen,
    _hDQconnected, hclDR, hclDQ, _hDRcompact, _hDQcompact, _hDRfrontier,
    _hDQfrontier, hKR, hKQ, hRQ, hpieces, _hpiecesRest⟩ :=
    decompose C hed a b hshape c hshift R Rh Q heR hRh heQ hy hout
      f hN hR hf.continuous hhN.continuous hhR.continuous bf bN bR
      gSp gSm gS2 bandN bandR
  change (K ∪ closure DR) ∪ closure DQ = W at hpieces
  obtain ⟨eta, heta, _hetacap, e, hsource, hsmooth, himage0, himage1raw,
    himage2raw, hlower0, hlower1, hlower2, hboundary⟩ :=
    products C hshape hep c hshift Rh Q heRh heQ f hN hR
      hf hhN hhR bf bN bR gSp gSm gS2
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
    M25.exists_circle_projection_on_clopen_three_piece_union Wo hWcompact.isClosed
      heta e hsource hsmooth hboundary hinter (hthree.trans hpieces)
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
  have hUW : U ⊆ W := fun _ hx => Or.inl (Or.inl hx)
  have hRhW : Rh.carrier ⊆ W := fun _ hx => Or.inl (Or.inr (hRhcarrier ▸ hx))
  have hQW : Q.carrier ⊆ W := fun _ hx => Or.inr hx
  have hneckCover : W = ⋃ A : {A // A ∈ necks}, A.1.carrier := by
    apply Subset.antisymm
    · intro x hxW
      rcases hxW with (hxU | hxR) | hxQ
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxU
        exact mem_iUnion.mpr ⟨⟨C.neck i, Or.inl ⟨i, hi, rfl⟩⟩, hxi⟩
      · exact mem_iUnion.mpr ⟨⟨Rh, Or.inr (mem_insert _ _)⟩, hRhcarrier.symm ▸ hxR⟩
      · exact mem_iUnion.mpr ⟨⟨Q, Or.inr (mem_insert_of_mem _ (mem_singleton _))⟩, hxQ⟩
    · intro x hx
      obtain ⟨⟨A, hA⟩, hxA⟩ := mem_iUnion.mp hx
      rcases hA with ⟨i, hi, rfl⟩ | hA
      · exact hUW (mem_iUnion₂.mpr ⟨i, hi, hxA⟩)
      · rcases mem_insert_iff.mp hA with rfl | hA
        · exact hRhW hxA
        · obtain rfl := mem_singleton_iff.mp hA
          exact hQW hxA
  have enlarge {V S T : Set M} (hV : V ⊆ W) (h : SmoothSphereIsotopicIn V S T) :
      SmoothSphereIsotopicIn W S T := by
    obtain ⟨F, hF, ht, hstart, hend⟩ := h
    exact ⟨F, hF, fun t ht' => ⟨(ht t ht').1, (ht t ht').2.trans hV⟩, hstart, hend⟩
  have hRhSp : SmoothSphereIsotopicIn Rh.carrier Rh.central_sphere Sp := by
    have hzero (_q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-Rh.epsilon⁻¹) Rh.epsilon⁻¹ :=
      Rh.zero_mem_interval
    have hfdomain (q : UnitTwoSphere) : f q ∈ Ioo (-Rh.epsilon⁻¹) Rh.epsilon⁻¹ := by
      rw [heRh]
      change f q ∈ Ioo (-L) L
      constructor <;> linarith only [hL, (bf q).1, (bf q).2]
    have h := Rh.m25_coordinate_graphs_isotopic (fun _ => 0) f
      contMDiff_const hf hzero hfdomain
    rw [Rh.coordinate_zero_range, ← gSp] at h
    exact h
  have hQSm : SmoothSphereIsotopicIn Q.carrier Q.central_sphere Sm := by
    have hzero (_q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ :=
      Q.zero_mem_interval
    have hcdomain (_q : UnitTwoSphere) : c ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ := by
      rw [heQ]
      change c ∈ Ioo (-L) L
      constructor <;> linarith only [hL, hshift.1, hshift.2]
    have h := Q.m25_coordinate_graphs_isotopic (fun _ => 0) (fun _ => c)
      contMDiff_const contMDiff_const hzero hcdomain
    rw [Q.coordinate_zero_range, ← gSm] at h
    exact h
  have hfiber0 : (Subtype.val : Wo → M) ''
      (p ⁻¹' {M25.Topology3D.periodCircleParam 3 0}) = Sm := by
    have h := (hseams 0).trans hlower0
    simpa only [Fin.val_zero, Nat.cast_zero] using h
  have hfiber1 : (Subtype.val : Wo → M) ''
      (p ⁻¹' {M25.Topology3D.periodCircleParam 3 1}) = Sp := by
    have h := (hseams 1).trans hlower1
    simpa only [Fin.val_one, Nat.cast_one] using h
  have hisotopy (A : EpsilonNeck g) (hA : A ∈ necks) : ∃ z : UnitCircle,
      SmoothSphereIsotopicIn W A.central_sphere
        ((Subtype.val : Wo → M) '' (p ⁻¹' {z})) := by
    rcases hA with ⟨i, hi, rfl⟩ | hA
    · refine ⟨M25.Topology3D.periodCircleParam 3 1, ?_⟩
      rw [hfiber1]
      exact enlarge hUW (lastSlice C hshape hei i hi)
    · rcases mem_insert_iff.mp hA with rfl | hA
      · refine ⟨M25.Topology3D.periodCircleParam 3 1, ?_⟩
        rw [hfiber1]
        exact enlarge hRhW hRhSp
      · obtain rfl := mem_singleton_iff.mp hA
        refine ⟨M25.Topology3D.periodCircleParam 3 0, ?_⟩
        rw [hfiber0]
        exact enlarge hQW hQSm
  obtain ⟨F, hFcarrier, hFepsilon⟩ :=
    M25.exists_circle_certificate_on_compact_open_component Wo hWconnected hWcompact hX
      H.epsilon_pos (heg.trans hgcap) p hpcont hpsurj hpsmooth hcharts
      necks hnecks hneckCover hisotopy
  exact ⟨Q, F, hQP, hFepsilon, hFcarrier⟩

end PoincareConjecture
