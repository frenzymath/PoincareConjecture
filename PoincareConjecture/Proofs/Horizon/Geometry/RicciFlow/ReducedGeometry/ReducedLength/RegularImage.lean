import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.PathCongruence
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sard.EqualDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LExponentialGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T R : ℝ} {p : M}

theorem exists_regular_initial_of_mem_regularImage
    (G : LExponentialGeometry F T R p) {q : M} {τ : ℝ}
    (hq : (q, τ) ∈ G.regularImage) :
    ∃ Z, (Z, τ) ∈ G.toLExponentialFamily.regularDomain ∧ G.gamma Z τ = q := by
  have ht := G.regular_inverse_time (q, τ) hq
  have hs := G.regular_chart.map_target hq
  rw [G.regular_source] at hs
  have hforward := G.regular_chart.right_inv hq
  rw [G.regular_forward] at hforward
  refine ⟨(G.regular_chart.symm (q, τ)).1, ?_, ?_⟩
  · have heq : ((G.regular_chart.symm (q, τ)).1, τ) = G.regular_chart.symm (q, τ) :=
      Prod.ext rfl ht.symm
    exact heq.symm ▸ hs
  · simpa only [ht] using congrArg Prod.fst hforward

theorem exists_uniqueMinimizing_of_regular_point
    (G : LExponentialGeometry F T R p) {q : M} {τ : ℝ}
    (r : ReducedLengthRegularPoint F T R p q τ) :
    ∃ Z, G.gamma Z τ = q ∧ G.toLExponentialFamily.uniqueMinimizing Z τ := by
  obtain ⟨Z, hZ, _⟩ := G.minimizers_lift τ r.tau_pos r.tau_lt
    r.path r.path_start r.minimizing
  have hend : G.gamma Z τ = q :=
    (hZ ⟨r.tau_pos.le, le_rfl⟩).symm.trans r.path_end
  refine ⟨Z, hend, r.tau_pos, r.tau_lt, ?_, ?_⟩
  · apply r.minimizing.congr
    simpa only [G.path_eq] using hZ
  · intro q' hq0 hq1 hmin
    exact (r.unique_minimizing_path q' hq0 (hq1.trans hend) hmin).trans hZ

theorem exists_regular_value_slice
    (G : LExponentialGeometry F T R p) {τ : ℝ} (hτ : 0 < τ) (hR : τ < R)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, ∀ Z, G.gamma Z τ = q →
      Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) p :=
    ContinuousLinearEquiv.ofFinrankEq rfl
  have he : ContMDiff (𝓡 n) 𝓘(ℝ, TangentSpace (𝓡 n) p) ∞ e := e.contDiff.contMDiff
  have hγ : ContMDiff 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) ∞ (fun Z => G.gamma Z τ) := by
    intro Z
    have hn : univ ×ˢ Ioo 0 R ∈ 𝓝 (Z, τ) :=
      (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hτ, hR⟩
    exact (G.gamma_smooth.contMDiffAt hn).comp Z
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ (fun v => G.gamma (e v) τ) :=
    hγ.comp he
  obtain ⟨q, hq, hregular⟩ := Poincare.Manifold.exists_regular_value_equal_dimension hf hU hne
  refine ⟨q, hq, ?_⟩
  intro Z hZ
  have hbij := hregular (e.symm Z) (by simpa only [e.apply_symm_apply] using hZ)
  have hchain := mfderiv_comp (e.symm Z)
    ((hγ (e (e.symm Z))).mdifferentiableAt (by simp))
    ((he (e.symm Z)).mdifferentiableAt (by simp))
  rw [e.apply_symm_apply] at hchain
  have hsurj : Function.Surjective (G.toLExponentialFamily.sliceDifferential Z τ) := by
    intro v
    obtain ⟨w, hw⟩ := hbij.2 v
    have heval := congrArg (fun A => A w) hchain
    exact ⟨mfderiv (𝓡 n) 𝓘(ℝ, TangentSpace (𝓡 n) p) e (e.symm Z) w,
      heval.symm.trans hw⟩
  exact ⟨(LinearMap.injective_iff_surjective (V := EuclideanSpace ℝ (Fin n))).mpr hsurj,
    hsurj⟩

theorem dense_regularImage_slice [ConnectedSpace M]
    (G : LExponentialGeometry F T R p) (Q : ReducedLengthDifferentialTheory F T R)
    {τ : ℝ} (hτ : 0 < τ) (hR : τ < R) :
    Dense {q | (q, τ) ∈ G.regularImage} := by
  obtain ⟨V, hV, hVdense, _, hVreg⟩ := Q.regular_locus p τ hτ hR
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨q, ⟨hqU, hqV⟩, hqreg⟩ := G.exists_regular_value_slice hτ hR
    (hU.inter hV) (hVdense.inter_open_nonempty U hU hUne)
  obtain ⟨r⟩ := hVreg q hqV
  obtain ⟨Z, hZ, hmin⟩ := G.exists_uniqueMinimizing_of_regular_point r
  have hs : (Z, τ) ∈ G.regular_chart.source :=
    G.regular_source.symm ▸ (show (Z, τ) ∈ G.toLExponentialFamily.regularDomain from
      ⟨hmin, hqreg Z hZ⟩)
  refine ⟨q, hqU, ?_⟩
  have ht := G.regular_chart.map_source hs
  simpa only [G.regular_forward, hZ, regularImage, mem_ofPred_eq] using ht

end PoincareConjecture.LExponentialGeometry
