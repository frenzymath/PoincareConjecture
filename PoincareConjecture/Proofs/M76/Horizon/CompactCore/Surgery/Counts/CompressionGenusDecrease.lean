import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionEulerChange
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.OriginalComponentEulerSum
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionComponentCorrespondence
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.OriginalComponentGenusComparison
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.General.IndexedCompressionComplexity

set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains
open scoped BigOperators

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in

theorem compressionComplexity_decreases
    {Eold Enew X ι : Type*}
    [NormedAddCommGroup Eold] [NormedSpace ℝ Eold] [FiniteDimensional ℝ Eold]
    [NormedAddCommGroup Enew] [NormedSpace ℝ Enew] [FiniteDimensional ℝ Enew]
    [DecidableEq Eold] [DecidableEq Enew]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hN : PLDomain e N) (hNc : IsCompact N) (hcontain : F ∪ P.closedStrip ⊆ N)
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (Aold : SimplicialComplex ℝ Eold) (Anew : SimplicialComplex ℝ Enew)
    (hAold : Aold.faces.Finite) (hAnew : Anew.faces.Finite)
    (hdimOld : ∀ s ∈ Aold.faces, s.card ≤ 3)
    (hdimNew : ∀ s ∈ Anew.faces, s.card ≤ 3)
    {n m : ℕ}
    (pickOld : Fin n ↪ Aold.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (pickNew : Fin m ↪ Anew.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (gold : Eold → X) (gnew : Enew → X)
    (hgold : PolyhedralPLInCharts e gold Aold.space) (hgoldi : InjOn gold Aold.space)
    (hgnew : PolyhedralPLInCharts e gnew Anew.space) (hgnewi : InjOn gnew Anew.space)
    (S : Fin n → Set X) (T : Fin m → Set X)
    (hSimage : ∀ i, S i = gold '' (Aold.edgeComponentComplex (pickOld i)).space)
    (hTimage : ∀ k, T k = gnew '' (Anew.edgeComponentComplex (pickNew k)).space)
    (hScompact : ∀ i, IsCompact (S i)) (hSconn : ∀ i, IsConnected (S i))
    (hScover : (⋃ i, S i) = F)
    (hScomponents : ∀ i, ∀ x ∈ S i, connectedComponentIn F x = S i)
    (hSdisjoint : Pairwise fun i k => Disjoint (S i) (S k))
    (hTcompact : ∀ k, IsCompact (T k)) (hTconn : ∀ k, IsConnected (T k))
    (hTcover : (⋃ k, T k) = Fnew)
    (hTcomponents : ∀ k, ∀ x ∈ T k, connectedComponentIn Fnew x = T k)
    (hTdisjoint : Pairwise fun k l => Disjoint (T k) (T l))
    (phiNew : X → Enew)
    (hphiNew : ∀ i, LocallyPiecewiseAffineOn (phiNew ∘ (e i).symm) (e i).target)
    (hphiNewi : InjOn phiNew Fnew)
    (hinverseNew : ∀ z ∈ Anew.space, phiNew (gnew z) = z)
    (oldGenus : Fin n → ℕ) (newGenus : Fin m → ℕ)
    (hgenusOld : ∀ i, Nat.card (Aold.edgeComponentComplex (pickOld i)).vertices +
      Nat.card (Triangle
        (Aold.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * oldGenus i = Nat.card (Edge
        (Aold.edgeComponentComplex (pickOld i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hgenusNew : ∀ k, Nat.card (Anew.edgeComponentComplex (pickNew k)).vertices +
      Nat.card (Triangle
        (Anew.edgeComponentComplex (pickNew k)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * newGenus k = Nat.card (Edge
        (Anew.edgeComponentComplex (pickNew k)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hzeroSphere : ∀ k, newGenus k = 0 → Nonempty (ChartwisePLSphere e (T k))) :
    Wall.compressionComplexity ((List.finRange m).map newGenus) <
      Wall.compressionComplexity ((List.finRange n).map oldGenus) := by
  classical
  let Old := fun i => Aold.edgeComponentComplex (pickOld i)
  let New := fun k => Anew.edgeComponentComplex (pickNew k)
  have hOld (i) : (Old i).faces.Finite := hAold.subset (Aold.edgeComponentComplex_le _)
  have hNew (k) : (New k).faces.Finite := hAnew.subset (Anew.edgeComponentComplex_le _)
  have hOldSub (i) : (Old i).space ⊆ Aold.space :=
    SimplicialComplex.space_subset_of_le (Aold.edgeComponentComplex_le _)
  have hNewSub (k) : (New k).space ⊆ Anew.space :=
    SimplicialComplex.space_subset_of_le (Anew.edgeComponentComplex_le _)
  have hOldPL (i) : PolyhedralPLInCharts e gold (Old i).space :=
    hgold.restrict_finite (Old i) (hOld i) (hOldSub i)
  have hOldCover : (⋃ i, gold '' (Old i).space) = F := by
    simpa only [hSimage] using hScover
  have hNewCover : (⋃ k, gnew '' (New k).space) = Fnew := by
    simpa only [hTimage] using hTcover
  have hF : IsCompact F := hScover ▸ isCompact_iUnion hScompact
  have hFnewN : Fnew ⊆ N := by
    rw [hnew]
    rintro x (hx | hx)
    · exact hcontain (Or.inl hx.1)
    · exact hcontain (Or.inr (P.endDisks_subset_closedStrip hx))
  have hTsub (k) : T k ⊆ Fnew := fun _ hx => hTcover.subset (mem_iUnion.mpr ⟨k, hx⟩)
  obtain ⟨s, phi, CountOld, CountNew, hphi, hphii, hphiPL,
    hCountOld, hCountNew, hCountOldSpace, hCountNewSpace, hEuler⟩ :=
    P.exists_original_compression_euler_change hF hcut hsmall hlateral hN hNc hcontain
      Old gold hOld hOldPL hOldCover
  have hOldCount := surfaceEulerCount_eq_original_component_genus_sum
    Aold hAold hdimOld pickOld gold hgold hgoldi hOldCover phi
      (hphii.mono (subset_union_left.trans hcontain)) hphiPL
      CountOld hCountOld hCountOldSpace oldGenus hgenusOld
  have hNewCount := surfaceEulerCount_eq_original_component_genus_sum
    Anew hAnew hdimNew pickNew gnew hgnew hgnewi hNewCover phi
      (hphii.mono hFnewN) hphiPL CountNew hCountNew
      (hCountNewSpace.trans (congrArg (fun Z => phi '' Z) hnew.symm)) newGenus hgenusNew
  obtain ⟨c, q, same, _, _, _, hcap, _, _, _, hsame⟩ :=
    P.exists_unaffected_component_correspondence hcut hsmall hnew S T
      hScompact hSconn hScover hScomponents hSdisjoint
      hTcompact hTconn hTcover hTcomponents hTdisjoint
  have hSameGenus (i : {i : Fin n // i ≠ c}) :
      oldGenus i = newGenus (same i) := by
    apply original_component_genus_eq (Old i) (New (same i)) (hOld i) (hNew (same i))
      (fun t ht => hdimOld t (Aold.edgeComponentComplex_le _ ht))
      (fun t ht => hdimNew t (Anew.edgeComponentComplex_le _ ht))
      gold gnew phiNew (hOldPL i) (hgoldi.mono (hOldSub i))
      (hSimage i).symm ((hTimage (same i)).symm.trans (hsame i).symm)
      hphiNew (hphiNewi.mono ((hsame i).subset.trans (hTsub (same i))))
      (fun z hz => hinverseNew z (hNewSub (same i) hz))
      (oldGenus i) (newGenus (same i)) (hgenusOld i) (hgenusNew (same i))
  have hpositive (hne : q false ≠ q true) (b : Bool) : 0 < newGenus (q b) := by
    have hne' : q b ≠ q (!b) := by
      cases b with
      | false => exact hne
      | true => exact Ne.symm hne
    have hopposite := (hTdisjoint hne').mono_right (hcap (!b))
    have hnonsphere := P.cap_component_not_sphere_of_graph hcut hsmall hnew
      (hTsub (q b)) (hTcomponents (q b)) b (hcap b) hopposite rim hrim hessential
      phi hphi (hphii.mono ((hTsub (q b)).trans hFnewN)) hphiPL
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnonsphere (hzeroSphere (q b) hz)
  apply Wall.compressionComplexity_indexed_of_euler_change oldGenus newGenus
    c q same hSameGenus hpositive
  rwa [hOldCount, hNewCount] at hEuler

end PoincareConjecture.M76.OriginalDiskProduct
