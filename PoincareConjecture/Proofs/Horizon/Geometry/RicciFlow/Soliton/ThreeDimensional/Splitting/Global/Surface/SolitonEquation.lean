import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Level
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.PotentialRegularity











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}



theorem parallelGradient_factor_hessian
    {D : LeviCivitaData g} {r φ : M → ℝ}
    (hr : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient D r) (hz : HasZeroHessian D r)
    (hφ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ φ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hr (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hr (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hr (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    ∀ (y : zeroLevelSet r) (u v : TangentSpace (𝓡 n) y),
      h.leviCivitaData.hessian (φ ∘ zeroLevelIncl r) y u v =
        D.hessian φ (zeroLevelIncl r y)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl r) y u)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl r) y v) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hr (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hr (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hr (⊤ : Opens M) hreg 0 g
  let Dh := h.leviCivitaData
  have hi := contMDiff_openLevelIncl hr (⊤ : Opens M) hreg n 0
  have hm := regularLevelMetric_inner hr (⊤ : Opens M) hreg 0 g
  dsimp only
  intro y u v
  obtain ⟨B, hn, hB⟩ := Induced.exists_normal_hessian_correction D Dh hi y
    (Eventually.of_forall hm) u v
  have hlevel : r ∘ zeroLevelIncl r = fun _ : zeroLevelSet r => 0 :=
    funext fun z => z.2
  have hnormal : g.inner (zeroLevelIncl r y) (D.gradient r (zeroLevelIncl r y)) B = 0 := by
    have he := hB r (hr (zeroLevelIncl r y))
    rw [hlevel, hz] at he
    have hconst : Dh.hessian (fun _ => (0 : ℝ)) y u v = 0 := by
      simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
        mvfderiv_const, zero_apply, sub_zero]
    rw [hconst, zero_add] at he
    exact he.symm
  have hker : B ∈ (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) r (zeroLevelIncl r y)).ker := by
    change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) r (zeroLevelIncl r y) B = 0
    exact (D.inner_gradient r (zeroLevelIncl r y) B).symm.trans hnormal
  have hrange := range_mfderiv_openLevelIncl hr (⊤ : Opens M) hreg n 0 y
  have hBmem : B ∈ (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl r) y).range := by
    rw [hrange]
    exact hker
  obtain ⟨w, hw⟩ := hBmem
  change mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl r (⊤ : Opens M) 0) y w = B at hw
  have hBzero : B = 0 := by
    have he := hn w
    rw [hw] at he
    by_contra hne
    exact (ne_of_gt (g.pos (zeroLevelIncl r y) B hne)) he
  have he := hB φ (hφ (zeroLevelIncl r y))
  simpa only [hBzero, map_zero, add_zero] using he



theorem parallelGradient_factor_soliton_equation
    {D : LeviCivitaData g} {r φ : M → ℝ} {lambda : ℝ}
    (hr : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient D r) (hz : HasZeroHessian D r)
    (hφ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ x, ∀ u v : TangentSpace (𝓡 (n + 1)) x,
      D.ricci x u v + D.hessian φ x u v = lambda * g.inner x u v) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hr (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hr (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hr (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    ∀ (y : zeroLevelSet r) (u v : TangentSpace (𝓡 n) y),
      h.leviCivitaData.ricci y u v +
        h.leviCivitaData.hessian (φ ∘ zeroLevelIncl r) y u v =
          lambda * h.inner y u v := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hr (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hr (⊤ : Opens M) hreg n 0
  have hφsmooth := D.contMDiff_of_C2_gradient_soliton hφ hsol
  dsimp only
  intro y u v
  rw [(parallelGradient_factor_curvature hr hu hz y).2.2.1,
    parallelGradient_factor_hessian hr hu hz hφsmooth]
  exact hsol (zeroLevelIncl r y) _ _

end PoincareConjecture.RiemannianMetric
