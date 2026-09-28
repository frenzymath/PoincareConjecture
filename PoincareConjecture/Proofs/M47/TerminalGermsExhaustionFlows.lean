import PoincareConjecture.Proofs.M47.TerminalGermsPrecompactFlow
import PoincareConjecture.Proofs.M47.TerminalGermsDomainCompatibility
import PoincareConjecture.Proofs.M47.TerminalCurvatureNullLine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

theorem terminalGerms_exists_exhaustion_flows
    {n : ℕ} {ι : Type*} {P : ι → Type*} {M : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace M]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ M]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow n (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : P i) (y : P j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (q j) y c →
        mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (q j) y d →
        ((F i).metric t).inner x a b = ((F j).metric t).inner y c d)
    (g : RiemannianMetric n M)
    (hterminal : ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric 0).inner x a b = g.inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (E : ℕ → Set M) (hE : ∀ j, IsOpen (E j))
    (hconnected : ∀ j, IsConnected (E j))
    (hcompact : ∀ j, IsCompact (closure (E j)))
    (hnested : ∀ j, closure (E j) ⊆ E (j + 1))
    (hexhaust : (⋃ j, E j) = univ) :
    let U : ℕ → Opens M := fun j => ⟨E j, hE j⟩
    ∃ (s : ℕ → Finset ι) (delta : ℕ → ℝ),
      (∀ j, (s j).Nonempty) ∧
      (∀ j, closure (E j) ⊆ ⋃ i ∈ s j, range (q i)) ∧
      (∀ j, 0 < delta j) ∧ (∀ j i, i ∈ s j → delta j < tau i) ∧
      ∃ G : ∀ j, RicciFlow n (U j) (Icc (-delta j) 0),
        (∀ j (y : U j) (v w : TangentSpace (𝓡 n) y),
          ((G j).metric 0).inner y v w = g.inner y.val v w) ∧
        (∀ j t, t ∈ Icc (-delta j) 0 → ∀ i, t ∈ Icc (-tau i) 0 →
          ∀ (x : P i) (hx : q i x ∈ U j) (a b : TangentSpace (𝓡 n) x),
            ((F i).metric t).inner x a b = ((G j).metric t).inner ⟨q i x, hx⟩
              (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
              (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) ∧
        (∀ j l t, t ∈ Icc (-delta j) 0 → t ∈ Icc (-delta l) 0 →
          ∀ (y : M) (hyj : y ∈ U j) (hyl : y ∈ U l)
            (v w : EuclideanSpace ℝ (Fin n)),
            ((G j).metric t).inner ⟨y, hyj⟩ v w =
              ((G l).metric t).inner ⟨y, hyl⟩ v w) ∧
        (∀ x y z : M, ∃ j, x ∈ U j ∧ y ∈ U j ∧ z ∈ U j) := by
  classical
  let U : ℕ → Opens M := fun j => ⟨E j, hE j⟩
  have hex (j : ℕ) := terminalGerms_precompact_flow tau htau F q hq hcover
    hinv g hterminal (U j) (hconnected j).nonempty (hcompact j)
  choose s hsne hs delta hdelta htime G hzero hread using hex
  refine ⟨s, delta, hsne, hs, hdelta, htime, G, ?_, hread, ?_, ?_⟩
  · intro j y v w
    rw [hzero j, RiemannianMetric.pullbackOfLocalDiffeomorph_inner]
    simp only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
  · intro j l t htj htl y hyj hyl v w
    apply terminalGerms_domain_flows_compatibility tau F q hq (U j) (U l)
      (s j) ?_ (delta j) (delta l) (htime j) (G j) (G l)
      (hread j) (hread l) t htj htl y hyj hyl v w
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs j (subset_closure hz))
    obtain ⟨his, x, hx⟩ := mem_iUnion.mp hi
    exact ⟨i, his, x, hx⟩
  · have hmono : Monotone E := monotone_nat_of_le_succ fun j =>
      subset_closure.trans (hnested j)
    exact terminalCurvature_exhaustion_triple U hmono hexhaust

end PoincareConjecture.M47
