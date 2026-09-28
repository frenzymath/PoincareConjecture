import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.SeparationEvolution
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductFlow







noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture





theorem m64AnnulusEvolution_of_M63
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Icc a b)}
    (G : M63AmbientGeometry F) (analytic : M63AnalyticConclusion F G)
    (hcompact : IsCompact (univ : Set M)) (hn : 1 ≤ n) :
    M64AnnulusEvolution G := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hst⟩ := F.nontrivial.exists_lt
    exact hs.1.trans_lt (hst.trans_le ht.2)
  refine {
    curvature_bounded := fun _ ht => m64CurvatureRange_bddAbove_of_compact hcompact ht
    curvature_nonnegative := fun _ ht =>
      m64CurvatureSupremum_nonneg (m64CurvatureRange_bddAbove_of_compact hcompact ht)
    curvature_continuous := m64CurvatureSupremum_continuous_of_compact hcompact
    curves := ?_ }
  intro circumference h c0 c1 hc0 hc1 hr0 hr1 _hd0 _hd1 A0
  let P := G.product circumference h
  let : Fact (0 < circumference) := ⟨h⟩
  obtain ⟨Q⟩ := M62.nonempty_circleProductData P.flow 1 (by norm_num)
  have hramp0 := (analytic.preservation circumference h b hab le_rfl c0 hc0 hr0).positive
  have hramp1 := (analytic.preservation circumference h b hab le_rfl c1 hc1 hr1).positive
  have hest := M64.auxiliaryCircle_ramp_evolution P Q hn hc0 hc1
    (fun t ht => hramp0 t (Ioo_subset_Icc_self ht))
    (fun t ht => hramp1 t (Ioo_subset_Icc_self ht)) A0 G.nonnegative.1 G.bounds
  exact {
    nonempty := m64AnnulusFlow_nonempty_of_initial hcompact h P hc0 hc1 A0
    bounded_below := fun _ _ => m64AnnulusAreaRange_bddBelow _ _ _
    nonnegative := m64AnnulusFlow_nonnegative_of_initial hcompact h P hc0 hc1 A0
    continuous := m64AnnulusFlow_continuous_of_initial hcompact h P hc0 hc1 A0
    forward := hest.1
    exponential := hest.2 }

end PoincareConjecture
