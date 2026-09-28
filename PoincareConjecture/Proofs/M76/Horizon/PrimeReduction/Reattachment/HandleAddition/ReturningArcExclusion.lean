import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningArcMinimumContradiction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalPlanarReturningDisk

set_option autoImplicit false
open Set Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
noncomputable local instance returningArcExclusionDecidableEq : DecidableEq P2 :=
  fun _ _ => Classical.propDecidable _

theorem ChartwisePLSphere.no_returning_disk_at_essential_minimum
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
    {S : Set X} (s : ChartwisePLSphere e S)
    (hgs : g '' K.space = S ∩ R)
    (hcross : ∀ x ∈ S ∩ frontier R, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier R ↔ H y 0 = 0) :
    ¬∃ i,∃ D U : Set P2,
      IsFinitePLBallPair P2 D (U ∪ C.pieces i) ∧
      IsFinitePLBallPair ℝ U (U ∩ C.pieces i) ∧
      D ⊆ K.space ∧ D ∩ rim = U := by
  classical
  rintro ⟨i,D,U,hD,hU,hDK,hDrim⟩
  have hrims : ∀ x ∈ J.space,∀ y ∈ K.space,f x = g y → (x ∈ q ↔ y ∈ rim) := by
    intro x hx y hy hxy
    rw [←hfproper x hx,←hgproper y hy,hxy]
  have hCarcs := C.interval_models_of_paired_intervals M hfi hgi hrims harcs
  obtain ⟨j,A,V,T,hA,hV,hAK,hArim,hcontact,hT,hcover,hcommon⟩ :=
    s.exists_original_outermost_returning_disk he K hK g hg hgi hgs hgproper
      hcross C hCarcs i hD hU hDK hDrim
  exact false_of_outermost_returning_disk_at_essential_minimum hR he J K hJ hK
    hJball hf hg hfi hgi hfR hgR hfproper hgproper hfno hboundary hinterior
    hminimum C M harcs j hA hV hAK hArim hcontact hT hcover.symm.subset hcommon

end PoincareConjecture.M76
