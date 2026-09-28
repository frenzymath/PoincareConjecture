import PoincareConjecture.Proofs.M47.TerminalCurvatureAmbientParallel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.UnitCover










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting



theorem terminalCurvature_prescribed_parallel_section
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hrank : ∀ y, ricciNullity D y = 1)
    {ι : Type*} (U : ι → Opens M) (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow n (U i) (Icc (-tau i) 0))
    (hmetric : ∀ i (y : U i) (v w : TangentSpace (𝓡 n) y),
      ((F i).metric 0).inner y v w = g.inner y.val v w)
    (hsec : ∀ i t, t ∈ Icc (-tau i) 0 → ((F i).connection t).NonnegativeSectionalCurvature)
    (hcover : ∀ y : M, ∃ i, y ∈ U i) (p : UnitRicciKernel D) :
    ∃ (O : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen O ∧ p.val.proj ∈ O ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) O ∧ V p.val.proj = p.val.snd ∧
      ∀ y ∈ O, g.inner y (V y) (V y) = 1 ∧
        (∀ w, D.ricci y (V y) w = 0) ∧ ∀ w, D.connection V y w = 0 := by
  obtain ⟨O, V, hO, hp, hV, hVp, hnull⟩ := exists_local_smooth_unit_ricci_null_section
    D (hC.tensor_calculus n M g D)
    (Eventually.of_forall fun y => (hrank y).trans (hrank p.val.proj).symm)
    p.val.snd p.property.2 p.property.1
  refine ⟨O, V, hO, hp, hV, hVp, fun y hy => ⟨(hnull y hy).1, (hnull y hy).2, ?_⟩⟩
  intro w
  obtain ⟨i, hi⟩ := hcover y
  exact terminalCurvature_parallel_from_open_germ D hC (U i)
    (show -tau i < 0 by linarith [htau i]) (F i) (hmetric i) (hsec i) V ⟨y, hi⟩
    (hV.contMDiffAt (hO.mem_nhds hy))
    (mem_of_superset (hO.mem_nhds hy) fun z hz => (hnull z hz).2)
    (mem_of_superset (hO.mem_nhds hy) fun z hz => (hnull z hz).1) (hrank y) w

end PoincareConjecture.M47
