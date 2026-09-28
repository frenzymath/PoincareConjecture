import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedSphereCollarInterval
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CenteredCollarRawMarks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.GlobalExteriorDiskProduct

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.original_relative_centered_collar_cut
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (F : X → E) (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S) (hNc : IsCompact N)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (N ×ˢ Icc (-1 : ℝ) 1))
    (hi : InjOn c (N ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1)
    (hinside : MapsTo c (N ×ˢ Icc (-ε) ε) (interior R))
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-ε) ε)))
    (hzero : S = c '' (N ×ˢ ({0} : Set ℝ))) :
    let O := c '' (N ×ˢ Ioo (-ε) ε)
    let Q := R \ O
    ∃ (B : Bool → Set X) (_sB : ∀ i, ChartwisePLSphere e (B i))
      (W : (N × unitInterval) ≃ₜ closure O),
      IsCompact Q ∧ PLDomain e Q ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, B i ⊆ closure O) ∧ frontier O = B false ∪ B true ∧
      frontier Q = frontier R ∪ ⋃ i, B i ∧
      closure O ⊆ interior R ∧
      (∀ z, (W z : X) ∈ O ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2) ∧ S ⊆ closure O := by
  classical
  let K := c '' (N ×ˢ Icc (-ε) ε)
  let O := c '' (N ×ˢ Ioo (-ε) ε)
  have hci : Topology.IsEmbedding (fun z : (N ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z) := by
    let : CompactSpace (N ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp (hNc.prod isCompact_Icc)
    exact hc.continuousOn.domRestrict.isClosedEmbedding
      (fun z w h => Subtype.ext (hi z.property w.property h)) |>.isEmbedding
  obtain ⟨hK,hKPL,hKi,hend,hendDis,hKfront⟩ :=
    s.closed_bicollar_interval_domain he.compatible he.cover F hF hFi hN hNc c hc hci
      (by linarith : -1 < -ε) (by linarith : -ε < ε) hεsmall hopen
  have hKR : K ⊆ interior R := image_subset_iff.mpr hinside
  obtain ⟨hQ,hQPL,_,_,hQfront⟩ := he.interior_removal_geometry hR hKPL hKR
  have hQeq : R ∩ (interior K)ᶜ = R \ O := by rw [hKi]; rfl
  rw [hQeq] at hQ hQPL hQfront
  let B : Bool → Set X := fun b => c '' (N ×ˢ {if b then ε else -ε})
  let sB (b : Bool) := Classical.choice (hend b)
  have hclosure : closure O = K := hc.continuousOn.closure_image_collar_strip hNc hε hεsmall.le
  have hBsub (b) : B b ⊆ closure O := by
    rw [hclosure]
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨z,⟨hz.1,?_⟩,rfl⟩
    have ht : z.2 = if b then ε else -ε := hz.2
    rw [ht]
    cases b <;> simp only [Bool.false_eq_true,reduceIte] <;> constructor <;> linarith
  have hBdis : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    cases i <;> cases j <;> first | contradiction | exact hendDis | exact hendDis.symm
  have hOf : frontier O = B false ∪ B true := by
    rw [frontier,hclosure,hopen.interior_eq,←hKi]
    simpa only [hK.isClosed.frontier_eq,B,K] using hKfront
  have hQf : frontier (R \ O) = frontier R ∪ ⋃ i, B i := by
    rw [hQfront,hKfront]
    ext x
    simp only [B,mem_union,mem_iUnion,Bool.exists_bool,ite_true,ite_false,Bool.false_eq_true]
    tauto
  obtain ⟨W,_,hWO,hWS,hSC⟩ := exists_centered_collar_raw_marks hNc c hc.continuousOn hi
    hε hεsmall.le hzero
  exact ⟨B,sB,W,hQ,hQPL,hBdis,hBsub,hOf,hQf,hclosure.subset.trans hKR,hWO,hWS,hSC⟩

end PoincareConjecture.M76
