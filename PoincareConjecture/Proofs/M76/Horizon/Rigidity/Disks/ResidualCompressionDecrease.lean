import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionGenusDecrease
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ResidualCompressionComplexity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels










set_option autoImplicit false
open Set Metric Geometry
open scoped BigOperators

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

open Classical in
theorem residualComplexity_decreases
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
    (oldResidual : Fin n → ℕ) (newResidual : Fin m → ℕ)
    (hcountOld : ∀ i, (Aold.edgeComponentComplex (pickOld i)).surfaceEulerCount =
      2 - (oldResidual i : ℤ))
    (hcountNew : ∀ k, (Anew.edgeComponentComplex (pickNew k)).surfaceEulerCount =
      2 - (newResidual k : ℤ))
    (hzeroSphere : ∀ k, newResidual k = 0 → Nonempty (ChartwisePLSphere e (T k))) :
    (∑ k, (newResidual k - 1)) < ∑ i, (oldResidual i - 1) := by
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
  obtain ⟨s, phi, CountOld, CountNew, hc, hi, hpl,
    hCOld, hCNew, hCOldSpace, hCNewSpace, hEuler⟩ :=
    P.exists_original_compression_euler_change hF hcut hsmall hlateral hN hNc hcontain
      Old gold hOld hOldPL hOldCover
  have hOldCount := surfaceEulerCount_eq_original_component_sum
    Aold hAold hdimOld pickOld gold hgold hgoldi hOldCover phi
      (hi.mono (subset_union_left.trans hcontain)) hpl CountOld hCOld hCOldSpace
  have hNewCount := surfaceEulerCount_eq_original_component_sum
    Anew hAnew hdimNew pickNew gnew hgnew hgnewi hNewCover phi
      (hi.mono hFnewN) hpl CountNew hCNew
      (hCNewSpace.trans (congrArg (fun Z => phi '' Z) hnew.symm))
  obtain ⟨c, q, same, _, _, _, hcap, _, _, _, hsame⟩ :=
    P.exists_unaffected_component_correspondence hcut hsmall hnew S T
      hScompact hSconn hScover hScomponents hSdisjoint
      hTcompact hTconn hTcover hTcomponents hTdisjoint
  have hSame (i : {i : Fin n // i ≠ c}) : oldResidual i = newResidual (same i) := by
    have h := original_component_surfaceEulerCount_eq (Old i) (New (same i))
      (hOld i) (hNew (same i))
      (fun t ht => hdimOld t (Aold.edgeComponentComplex_le _ ht))
      (fun t ht => hdimNew t (Anew.edgeComponentComplex_le _ ht))
      gold gnew phiNew (hOldPL i) (hgoldi.mono (hOldSub i))
      (hSimage i).symm ((hTimage (same i)).symm.trans (hsame i).symm)
      hphiNew (hphiNewi.mono ((hsame i).subset.trans (hTsub (same i))))
      (fun z hz => hinverseNew z (hNewSub (same i) hz))
    rw [hcountOld, hcountNew] at h
    omega
  have hpositive (hne : q false ≠ q true) (b : Bool) : 0 < newResidual (q b) := by
    have hne' : q b ≠ q (!b) := by
      cases b with
      | false => exact hne
      | true => exact Ne.symm hne
    have hopposite := (hTdisjoint hne').mono_right (hcap (!b))
    have hnonsphere := P.cap_component_not_sphere_of_graph hcut hsmall hnew
      (hTsub (q b)) (hTcomponents (q b)) b (hcap b) hopposite rim hrim hessential
      phi hc (hi.mono ((hTsub (q b)).trans hFnewN)) hpl
    exact Nat.pos_of_ne_zero (fun hz => hnonsphere (hzeroSphere (q b) hz))
  apply residualComplexity_decreases_of_euler_change oldResidual newResidual c q same hSame hpositive
  simpa only [hOldCount, hNewCount, hcountOld, hcountNew] using hEuler


theorem frontierResidualModel_complexity_decreases
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew N Nold Nnew : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hN : PLDomain e N) (hNc : IsCompact N) (hcontain : F ∪ P.closedStrip ⊆ N)
    (hFnew : Fnew ⊆ Nnew)
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (oldModel : FrontierResidualModel e Nold F)
    (newModel : FrontierResidualModel e Nnew Fnew) :
    newModel.complexity < oldModel.complexity := by
  classical
  exact P.residualComplexity_decreases hcut hsmall hlateral hnew hN hNc hcontain
    rim hrim hessential oldModel.complex newModel.complex
    oldModel.finite newModel.finite oldModel.dimension newModel.dimension
    oldModel.pick newModel.pick oldModel.map newModel.map
    oldModel.pl oldModel.injective newModel.pl newModel.injective
    oldModel.components newModel.components oldModel.images newModel.images
    (fun i => (oldModel.component i).1) (fun i => (oldModel.component i).2.1)
    oldModel.cover (fun i => (oldModel.component i).2.2.2) oldModel.disjoint
    (fun k => (newModel.component k).1) (fun k => (newModel.component k).2.1)
    newModel.cover (fun k => (newModel.component k).2.2.2) newModel.disjoint
    newModel.coordinates newModel.coordinates_pl (newModel.coordinates_injective.mono hFnew)
    newModel.inverse oldModel.residual newModel.residual oldModel.euler newModel.euler
    newModel.zero_sphere

end PoincareConjecture.M76.OriginalDiskProduct
