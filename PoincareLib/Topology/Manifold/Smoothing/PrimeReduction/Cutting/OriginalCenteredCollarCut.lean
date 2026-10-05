import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.ClosedSphereCollarInterval
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.CenteredCollarRawMarks
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.GlobalExteriorDiskProduct

/-!
# The original centered collar as a compact marked PL cut

The literal strip supplies the cut domain, its whole boundary spheres,
and the same raw-complement product used by component comparison.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76

theorem ChartwisePLSphere.original_centered_collar_cut
    {X E ι ν : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (F : X → E) (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S) (hNc : IsCompact N)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (N ×ˢ Icc (-1 : ℝ) 1))
    (hi : InjOn c (N ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1)
    (hinside : MapsTo c (N ×ˢ Icc (-ε) ε) (interior R))
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-ε) ε)))
    (hzero : S = c '' (N ×ˢ ({0} : Set ℝ)))
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hBfront : frontier R = ⋃ i, B i) :
    let O := c '' (N ×ˢ Ioo (-ε) ε)
    let Q := R \ O
    ∃ (D : ν ⊕ Bool → Set X) (_sD : ∀ i, ChartwisePLSphere e (D i))
      (W : (N × unitInterval) ≃ₜ closure O),
      IsCompact Q ∧ PLDomain e Q ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧ frontier Q = ⋃ i, D i ∧
      closure O ⊆ interior R ∧
      (∀ z, (W z : X) ∈ O ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1 / 2) ∧ S ⊆ closure O := by
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
  let send (b : Bool) := Classical.choice (hend b)
  let D : ν ⊕ Bool → Set X := Sum.elim B (fun b => c '' (N ×ˢ {if b then ε else -ε}))
  let sD : ∀ i, ChartwisePLSphere e (D i) := fun i => by
    cases i with
    | inl i => exact sB i
    | inr b => exact send b
  have hcross (i : ν) (b : Bool) : Disjoint (D (.inl i)) (D (.inr b)) := by
    apply disjoint_left.mpr
    intro x hxB hxD
    have hxR : x ∈ frontier R := hBfront.symm.subset (mem_iUnion.mpr ⟨i,hxB⟩)
    have hxK : x ∈ K := by
      rcases hxD with ⟨z,hz,rfl⟩
      refine ⟨z,⟨hz.1,?_⟩,rfl⟩
      have ht : z.2 = if b then ε else -ε := hz.2
      rw [ht]
      cases b <;> simp only [Bool.false_eq_true,reduceIte] <;> constructor <;> linarith
    exact hxR.2 (hKR hxK)
  have hDdis : Pairwise fun i j => Disjoint (D i) (D j) := by
    intro i j hij
    cases i with
    | inl i => cases j with
      | inl j => exact hBdis (fun h => hij (congrArg Sum.inl h))
      | inr b => exact hcross i b
    | inr b => cases j with
      | inl i => exact (hcross i b).symm
      | inr a => cases b <;> cases a
                  <;> simp only [ne_eq,not_true_eq_false] at hij
                  <;> first | contradiction | exact hendDis | exact hendDis.symm
  have hDf : frontier (R \ O) = ⋃ i, D i := by
    rw [hQfront,hKfront,hBfront]
    ext x
    simp only [D,mem_union,mem_iUnion,Sum.exists,Sum.elim_inl,Sum.elim_inr,
      Bool.exists_bool,ite_true]
    tauto
  have hclosure : closure O = K := hc.continuousOn.closure_image_collar_strip hNc hε hεsmall.le
  obtain ⟨W,_,hWO,hWS,hSC⟩ := exists_centered_collar_raw_marks hNc c hc.continuousOn hi hε hεsmall.le hzero
  exact ⟨D,sD,W,hQ,hQPL,hDdis,hDf,hclosure.subset.trans hKR,hWO,hWS,hSC⟩

end PoincareMT.M76
