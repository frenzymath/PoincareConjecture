import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionRefinement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideCancellation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Triangulation
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Incidence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem sum_zero_of_pairwise_neg
    {A : Type*} [Fintype A] [Nontrivial A] (term : A → ℝ)
    (hpair : ∀ a b, a ≠ b → term a + term b = 0) : ∑ a, term a = 0 := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  by_cases hex : ∃ c : A, c ≠ a ∧ c ≠ b
  · obtain ⟨c, hca, hcb⟩ := hex
    have ha : term a = 0 := by
      have h₁ := hpair a b hab
      have h₂ := hpair c a hca
      have h₃ := hpair c b hcb
      linarith
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = a
    · simpa only [hx] using ha
    · have h := hpair x a hx
      linarith
  · have huniv : (Finset.univ : Finset A) = {a, b} := by
      ext c
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      by_contra hc
      exact hex ⟨c, not_or.mp hc⟩
    rw [huniv, Finset.sum_pair hab]
    exact hpair a b hab

open Classical in
private theorem sum_eq_unpaired_fibers
    {A E : Type*} [Fintype A] [Finite E] (slot : A → E) (term : A → ℝ)
    (hpair : ∀ a b, a ≠ b → slot a = slot b → term a + term b = 0) :
    (∑ a, term a) = ∑ a, if ∀ b, slot b = slot a → b = a then term a else 0 := by
  classical
  let _ := Fintype.ofFinite E
  let cut (a : A) := if ∀ b, slot b = slot a → b = a then term a else 0
  have hsum (f : A → ℝ) : (∑ a, f a) = ∑ e, ∑ a : {a // slot a = e}, f a.1 := by
    have h := (Equiv.sigmaFiberEquiv slot).sum_comp f
    change (∑ a : (e : E) × {a // slot a = e}, f a.2.1) = ∑ a, f a at h
    simpa only [Fintype.sum_sigma] using h.symm
  change (∑ a, term a) = ∑ a, cut a
  rw [hsum term, hsum cut]
  apply Finset.sum_congr rfl
  intro e _
  rcases subsingleton_or_nontrivial {a // slot a = e} with hs | hn
  · let _ := hs
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [cut]
    rw [if_pos]
    intro b hb
    exact congrArg Subtype.val (Subsingleton.elim (⟨b, hb.trans a.2⟩ : {a // slot a = e}) a)
  · let _ := hn
    have hzero : (∑ a : {a // slot a = e}, term a.1) = 0 := by
      apply sum_zero_of_pairwise_neg
      intro a b hab
      exact hpair a.1 b.1 (fun h => hab (Subtype.ext h)) (a.2.trans b.2.symm)
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro a _
    dsimp only [cut]
    apply if_neg
    intro ha
    obtain ⟨b, hb⟩ := exists_ne a
    exact hb (Subtype.ext (ha b.1 (b.2.trans a.2.symm)))

open Classical in

theorem m64Intrinsic_region_turning_eq_unpaired
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hfront : ∀ i j, i ≠ j → (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F i) (b i))) :
    (∑ i, ∑ k : Fin 3, coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1)) =
      ∑ p : I × Fin 3, if ∀ q : I × Fin 3,
          faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
        coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
      else 0 := by
  classical
  let _ := Fintype.ofFinite (FaceBoundaryEdge face)
  let slot (p : I × Fin 3) := faceBoundaryIndex face p.1 p.2
  let term (p : I × Fin 3) :=
    coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
  have himage (i : I) (k : Fin 3) :
      (fun t : ℝ => F i (AffineMap.lineMap (b i (k + 1)) (b i ((k + 1) + 1)) t)) '' Icc (0 : ℝ) 1 =
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 := by
    rw [coordinateTriangle_cyclic_boundary_image, hboundary, image_comp]
    congr 1
    unfold affineSegment
    apply image_congr
    intro t _
    simp only [affineChartSegment, AffineMap.lineMap_apply_module]
    module
  have hpair (p q : I × Fin 3) (hpq : p ≠ q) (he : slot p = slot q) :
      term p + term q = 0 := by
    have hij : p.1 ≠ q.1 := by
      intro h
      apply hpq
      apply Prod.ext h
      apply Euler.coordinate_faceBoundaryIndex_injective face F b hsource hboundary q.1
      simpa only [slot, h] using he
    apply coordinateTriangleTurningIntegral_pair_eq_zero D (F p.1) (F q.1) (b p.1) (b q.1)
      (hF p.1) (hFi p.1) (hF q.1) (hFi q.1) (hsource p.1) (hsource q.1)
      (Q p.1) (Q q.1) (p.2 + 1) (q.2 + 1)
    · rw [himage, himage]
      exact (faceBoundaryIndex_eq_iff face p.1 q.1 p.2 q.2).mp he
    · rw [← hcarrier, ← hcarrier]
      apply disjoint_left.mpr
      intro x hx hy
      exact (hfront _ _ hij ⟨interior_subset hx, interior_subset hy⟩).2 hx
  have h := sum_eq_unpaired_fibers slot term hpair
  have hreindex (i : I) : (∑ k : Fin 3, term (i, k)) =
      ∑ k : Fin 3, coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 3))
      (fun k => coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1))
  simpa only [Fintype.sum_prod_type, hreindex, slot, term] using h

open Classical in

theorem m64Intrinsic_region_gaussBonnet_unpaired
    {I : Type*} [Fintype I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hfront : ∀ i j, i ≠ j → (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F i) (b i))) :
    (∫ x in ⋃ i, (face i).carrier, D.scalarCurvature x ∂g.volumeMeasure) +
      2 * (∑ p : I × Fin 3, if ∀ q : I × Fin 3,
          faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
        coordinateTriangleTurningIntegral D (F p.1) (b p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
        else 0) +
      2 * (∑ i, ∑ k : Fin 3, (Real.pi - coordinateTriangleAngle g (F i) (b i) k)) =
      4 * Real.pi * Fintype.card I := by
  classical
  have hcompact : IsCompact (⋃ i, (face i).carrier) :=
    isCompact_iUnion (fun i => (face i).isCompact_carrier)
  have hdisjoint : Pairwise (fun i j => AEDisjoint g.volumeMeasure
      (face i).carrier (face j).carrier) := fun i j hij =>
    measure_mono_null (hfront i j hij) ((face i).volumeMeasure_frontier_eq_zero g)
  have hint : (∑ i, ∫ x in F i '' convexHull ℝ (range (b i)),
      D.scalarCurvature x ∂g.volumeMeasure) =
      ∫ x in ⋃ i, (face i).carrier, D.scalarCurvature x ∂g.volumeMeasure := by
    have h := integral_iUnion_ae
      (fun i => (face i).isCompact_carrier.measurableSet.nullMeasurableSet)
      hdisjoint (D.continuous_scalarCurvature.continuousOn.integrableOn_compact hcompact)
    simpa only [tsum_fintype, hcarrier] using h.symm
  have hsum : (∑ i,
      ((∫ x in F i '' convexHull ℝ (range (b i)), D.scalarCurvature x ∂g.volumeMeasure) +
        2 * (∑ k : Fin 3, coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1)) +
        2 * (∑ k : Fin 3, (Real.pi - coordinateTriangleAngle g (F i) (b i) k)))) =
      ∑ _i : I, 4 * Real.pi :=
    Finset.sum_congr rfl (fun i _ =>
      gaussBonnet_coordinateTriangle_side_integrals D (F i) (b i) (hF i) (hFi i) (hsource i) (Q i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hint, m64Intrinsic_region_turning_eq_unpaired face F b hF hFi hsource
    hcarrier hboundary hfront D Q] at hsum
  nlinarith

end PoincareConjecture
