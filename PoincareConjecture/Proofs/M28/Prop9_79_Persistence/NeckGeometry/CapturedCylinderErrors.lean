import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CapturedCylinderJets
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.PullbackTails

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.M28.tube FiniteHessian

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem capturedCylinderCoordinates_error_germ
    {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {h : RiemannianMetric 3 X} (g : RiemannianMetric 3 M) (gX : RiemannianMetric 3 X)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) {s : ℝ} (p : M)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hp : e.symm (N.coordinate_map (q, s)) ∈ (extChartAt (𝓡 3) p).source) :
    (fun x => g.pullbackCoefficients (capturedCylinderMap e N q s) x -
        gX.pullbackCoefficients (cylinderNeckChart N q s) x) =ᶠ[𝓝 0]
      (fun x => (g.pullbackCoefficients (extChartAt (𝓡 3) p).symm
          (capturedCylinderCoordinates e N q s p x) -
        gX.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) p).symm)
          (capturedCylinderCoordinates e N q s p x)).bilinearComp
            (fderiv ℝ (capturedCylinderCoordinates e N q s p) x)
            (fderiv ℝ (capturedCylinderCoordinates e N q s p) x)) := by
  filter_upwards [(isOpen_capturedCylinderChartDomain e N hcapture q s p).mem_nhds
    (zero_mem_capturedCylinderChartDomain e N q hs p hp)] with x hx
  rw [capturedCylinderCoordinates_limit_coefficients g e N hcapture q s p hx,
    capturedCylinderCoordinates_source_coefficients gX e N hcapture q s p hx]
  ext v w
  rfl

theorem exists_capturedCylinder_metric_error_tail
    {ι : Type*} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold (𝓡 3) ∞ (X i)]
    {h : ∀ i, RiemannianMetric 3 (X i)} (g : RiemannianMetric 3 M)
    (gX : ∀ i, RiemannianMetric 3 (X i))
    (e : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X i) ∞)
    (N : ∀ i, EpsilonNeck (h i)) (hcapture : ∀ i, (N i).carrier ⊆ (e i).target)
    (q : ι → UnitTwoSphere) (s : ι → ℝ) (p : ι → M)
    (hs : ∀ i, s i ∈ Ioo (-(N i).epsilon⁻¹) (N i).epsilon⁻¹)
    (hp : ∀ i, (e i).symm ((N i).coordinate_map (q i, s i)) ∈
      (extChartAt (𝓡 3) (p i)).source) (m : ℕ) (stage : ι → ℕ)
    (hmap : HasUniformJetBoundsAt m
      (fun i => fderiv ℝ (capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i)))
      (fun _ => 0))
    (herror : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i, K ≤ stage i →
      ∀ r ≤ m, ‖iteratedFDeriv ℝ r
          ((gX i).pullbackCoefficients ((e i) ∘ (extChartAt (𝓡 3) (p i)).symm))
          (capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i) 0) -
        iteratedFDeriv ℝ r (g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm)
          (capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i) 0)‖ ≤ delta) :
    ∀ rho : ℝ, 0 < rho → ∃ K : ℕ, ∀ i, K ≤ stage i → ∀ r ≤ m,
      ‖iteratedFDeriv ℝ r (fun x =>
        g.pullbackCoefficients (capturedCylinderMap (e i) (N i) (q i) (s i)) x -
        (gX i).pullbackCoefficients (cylinderNeckChart (N i) (q i) (s i)) x) 0‖ ≤ rho := by
  let psi := fun i => capturedCylinderCoordinates (e i) (N i) (q i) (s i) (p i)
  let B := fun i => (gX i).pullbackCoefficients ((e i) ∘ (extChartAt (𝓡 3) (p i)).symm)
  let L := fun i => g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm
  have hzero (i : ι) :=
    zero_mem_capturedCylinderChartDomain (e i) (N i) (q i) (hs i) (p i) (hp i)
  have hpsi (i : ι) : ContDiffAt ℝ ∞ (psi i) 0 :=
    (contDiffOn_capturedCylinderCoordinates (e i) (N i) (hcapture i)
      (q i) (s i) (p i)).contDiffAt
        ((isOpen_capturedCylinderChartDomain (e i) (N i) (hcapture i)
          (q i) (s i) (p i)).mem_nhds (hzero i))
  have hB (i : ι) : ContDiffAt ℝ ∞ (B i) (psi i 0) :=
    (capturedCylinderCoordinates_atlas_regular (gX i) (e i) (N i) (hcapture i)
      (q i) (s i) (p i) (hzero i)).1
  have hL (i : ι) : ContDiffAt ℝ ∞ (L i) (psi i 0) :=
    g.contDiffAt_pullbackCoefficients ((contMDiffOn_extChartAt_symm (p i)).contMDiffAt
      ((isOpen_extChartAt_target (p i)).mem_nhds
        ((extChartAt (𝓡 3) (p i)).map_source (hzero i).2)))
  have hE : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i, K ≤ stage i →
      ∀ r ≤ m, ‖iteratedFDeriv ℝ r (fun y => L i y - B i y) (psi i 0)‖ ≤ delta := by
    intro delta hdelta
    obtain ⟨K, hK⟩ := herror delta hdelta
    refine ⟨K, fun i hi r hr => ?_⟩
    change ‖iteratedFDeriv ℝ r (L i - B i) (psi i 0)‖ ≤ delta
    rw [iteratedFDeriv_sub_apply
      ((hL i).of_le (by exact_mod_cast le_top))
      ((hB i).of_le (by exact_mod_cast le_top)), norm_sub_rev]
    exact hK i hi r hr
  have htail := exists_bilinear_pullback_error_tail m stage hmap hpsi
    (fun i => (hL i).sub (hB i)) hE
  intro rho hrho
  obtain ⟨K, hK⟩ := htail rho hrho
  refine ⟨K, fun i hi r hr => ?_⟩
  rw [((capturedCylinderCoordinates_error_germ g (gX i) (e i) (N i) (hcapture i)
    (q i) (p i) (hs i) (hp i)).iteratedFDeriv ℝ r).eq_of_nhds]
  exact hK i hi r hr

end PoincareConjecture.Proofs.M28.NeckTransfer
