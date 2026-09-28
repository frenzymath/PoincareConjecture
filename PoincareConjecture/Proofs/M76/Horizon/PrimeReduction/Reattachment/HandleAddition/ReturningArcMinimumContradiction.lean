import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningArcDecrease
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PairedContactIntervals



set_option autoImplicit false
open Set Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
noncomputable local instance returningArcMinimumDecidableEq : DecidableEq P2 :=
  fun _ _ => Classical.propDecidable _

theorem false_of_outermost_returning_disk_at_essential_minimum
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (J K : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) (hK : K.faces.Finite)
    {q rim : Set P2} (hJball : IsFinitePLBallPair P2 J.space q)
    {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f J.space) (hg : PolyhedralPLInCharts e g K.space)
    (hfi : InjOn f J.space) (hgi : InjOn g K.space)
    (hfR : MapsTo f J.space R) (hgR : MapsTo g K.space R)
    (hfproper : ∀ x ∈ J.space,f x ∈ frontier R ↔ x ∈ q)
    (hgproper : ∀ x ∈ K.space,g x ∈ frontier R ↔ x ∈ rim)
    (hfno : ¬∃ F : C(J.space,frontier R),∀ x : q,
      (F ⟨x,hJball.1 x.property⟩ : X) = f x)
    (hboundary : ∀ x ∈ J.space,f x ∈ g '' K.space → f x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f '' J.space) (g '' K.space) (f x) true,
        (∀ z ∈ B.coordinates.source,B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source,B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ J.space,f x ∈ g '' K.space → f x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' K.space) (f x) false))
    (hminimum : ∀ k : P2 → X,
      PolyhedralPLInCharts e k J.space → IsEmbedding (fun x : J.space => k x) →
      MapsTo k J.space R → (∀ x ∈ J.space,k x ∈ frontier R ↔ x ∈ q) →
      (¬∃ F : C(J.space,frontier R),∀ x : q,
        (F ⟨x,hJball.1 x.property⟩ : X) = k x) →
      (∀ x ∈ J.space,k x ∈ g '' K.space → k x ∈ frontier R →
        ∃ B : OriginalSurfacePairChart e (k '' J.space) (g '' K.space) (k x) true,
          (∀ z ∈ B.coordinates.source,B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source,B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) →
      (∀ x ∈ J.space,k x ∈ g '' K.space → k x ∈ interior R →
        Nonempty (OriginalSurfacePairChart e (k '' J.space) (g '' K.space) (k x) false)) →
      Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' (g '' K.space) : Set P2)) ≤
        Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (g '' K.space) : Set P2)))
    (C : SurfaceIntersectionComponents J.space K.space f g rim)
    (M : SurfaceIntersectionComponents K.space J.space g f q)
    (harcs : ∀ j,IsFinitePLBallPair ℝ (M.pieces j) (M.pieces j ∩ q))
    (i : C.right.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {D U E : Set P2}
    (hD : IsFinitePLBallPair P2 D (U ∪ C.pieces i))
    (hU : IsFinitePLBallPair ℝ U (U ∩ C.pieces i))
    (hDK : D ⊆ K.space) (hDrim : D ∩ rim = U)
    (hcontact : D ∩ (⋃ j,C.pieces j) = C.pieces i)
    (hE : IsCompact E) (hcover : K.space ⊆ D ∪ E) (hcommon : D ∩ E = C.pieces i) : False := by
  classical
  let := M.components_finite
  have hrims : ∀ x ∈ J.space,∀ y ∈ K.space,f x = g y → (x ∈ q ↔ y ∈ rim) := by
    intro x hx y hy hxy
    rw [←hfproper x hx,←hgproper y hy,hxy]
  obtain ⟨j,a,b,c,d,hab,hcd,hW,hZ,hWq,hZrim,haq,hbq,hcr,hdr,
    hproperW,_,himage,ha,hb,hrest⟩ :=
    C.exists_matched_interval_endpoints M hfi hgi hrims harcs i
  have hUZ : U ∩ C.pieces i = C.pieces i ∩ rim := by
    apply Subset.antisymm
    · exact fun x hx => ⟨hx.2,(hDrim.superset hx.1).2⟩
    · exact fun x hx => ⟨hDrim.subset ⟨hD.1 (Or.inr hx.1),hx.2⟩,hx.1⟩
  have hUends : U ∩ C.pieces i = {c,d} := hUZ.trans hZrim
  have htrace : D ∩ g ⁻¹' (f '' J.space) = C.pieces i := by
    rw [←hcontact,←C.cover,C.right_space]
    ext x
    exact ⟨fun h => ⟨h.1,hDK h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  have hpieces : ⋃ j,M.pieces j = J.space ∩ f ⁻¹' (g '' K.space) :=
    M.cover.symm.trans M.right_space
  have hgproper' (x : P2) (hx : x ∈ K.space) :
      g x ∈ frontier R ↔ x ∈ K.space ∩ rim :=
    (hgproper x hx).trans (and_iff_right hx).symm
  have hDrim' : D ∩ (K.space ∩ rim) = U := by
    rw [←inter_assoc,inter_eq_left.mpr hDK,hDrim]
  obtain ⟨k,hk,hki,hkR,hkp,_,_,hcount,hkno,hkb,hkin,_⟩ :=
    Dehn.Annuli.exists_essential_returning_arc_decrease hR he J K hJ hK hJball inter_subset_left
      hW haq hbq hab hproperW hD (hUends ▸ hU) hZ hUends hcd hDK hDrim'
      hE hcover hcommon hf hg hfi hgi hfR hgR hfproper hgproper' himage ha hb htrace
      hfno hrest hboundary hinterior M.pieces (fun j => (M.topology j).1.isClosed)
      M.disjoint hpieces (fun j => (M.topology j).2.1)
  exact (not_lt_of_ge (hminimum k hk hki hkR hkp hkno hkb hkin)) hcount

end PoincareConjecture.M76
