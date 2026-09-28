import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.FixedCylinderJets
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
  {g : RiemannianMetric 3 M}




theorem forwardCylinderCoordinates_source_coefficients
    {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (gX : RiemannianMetric 3 X)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck g)
    (hcapture : N.carrier ⊆ e.source) (q : UnitTwoSphere) (s : ℝ) (p : M)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ cylinderNeckChartDomain N q s)
    (hp : cylinderNeckChart N q s x ∈ (extChartAt (𝓡 3) p).source) :
    gX.pullbackCoefficients (e ∘ cylinderNeckChart N q s) x =
      (gX.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) p).symm)
        ((extChartAt (𝓡 3) p) (cylinderNeckChart N q s x))).bilinearComp
          (fderiv ℝ ((extChartAt (𝓡 3) p) ∘ cylinderNeckChart N q s) x)
          (fderiv ℝ ((extChartAt (𝓡 3) p) ∘ cylinderNeckChart N q s) x) := by
  let c := extChartAt (𝓡 3) p
  let f := cylinderNeckChart N q s
  let psi := c ∘ f
  let e₀ := (Diffeomorph.refl (𝓡 3) M ∞).toPartialDiffeomorph
  have hcap₀ : N.carrier ⊆ e₀.target := fun _ _ => mem_univ _
  have hx₀ : x ∈ capturedCylinderChartDomain e₀ N q s p := ⟨hx, hp⟩
  have hU := isOpen_capturedCylinderChartDomain e₀ N hcap₀ q s p
  have hpsi : ContDiffAt ℝ ∞ psi x :=
    (contDiffOn_capturedCylinderCoordinates e₀ N hcap₀ q s p).contDiffAt (hU.mem_nhds hx₀)
  have hcinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (psi x) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (c.map_source hp))
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e (c.symm (psi x)) := by
    rw [show c.symm (psi x) = f x from c.left_inv hp]
    exact e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds
      (hcapture (cylinderNeckChart_mem_carrier N q s hx)))
  have heq : (e ∘ c.symm) ∘ psi =ᶠ[𝓝 x] e ∘ f := by
    filter_upwards [hU.mem_nhds hx₀] with y hy
    change e (c.symm (c (f y))) = e (f y)
    have hfy : f y ∈ c.source := hy.2
    rw [c.left_inv hfy]
  rw [← gX.pullbackCoefficients_eq_of_eventuallyEq heq]
  exact gX.pullbackCoefficients_comp ((he.comp (psi x) hcinv).mdifferentiableAt (by simp))
    (hpsi.differentiableAt (by simp))




theorem forwardCylinderCoordinates_error_germ
    {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (gX : RiemannianMetric 3 X)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck g)
    (hcapture : N.carrier ⊆ e.source) (q : UnitTwoSphere) {s : ℝ} (p : M)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hp : N.coordinate_map (q, s) ∈ (extChartAt (𝓡 3) p).source) :
    (fun x => gX.pullbackCoefficients (e ∘ cylinderNeckChart N q s) x -
        g.pullbackCoefficients (cylinderNeckChart N q s) x) =ᶠ[𝓝 0]
      (fun x => (gX.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) p).symm)
          ((extChartAt (𝓡 3) p) (cylinderNeckChart N q s x)) -
        g.pullbackCoefficients (extChartAt (𝓡 3) p).symm
          ((extChartAt (𝓡 3) p) (cylinderNeckChart N q s x))).bilinearComp
            (fderiv ℝ ((extChartAt (𝓡 3) p) ∘ cylinderNeckChart N q s) x)
            (fderiv ℝ ((extChartAt (𝓡 3) p) ∘ cylinderNeckChart N q s) x)) := by
  let e₀ := (Diffeomorph.refl (𝓡 3) M ∞).toPartialDiffeomorph
  have hcap₀ : N.carrier ⊆ e₀.target := fun _ _ => mem_univ _
  have hzero := zero_mem_capturedCylinderChartDomain e₀ N q hs p hp
  filter_upwards [(isOpen_capturedCylinderChartDomain e₀ N hcap₀ q s p).mem_nhds hzero]
    with x hx
  rw [forwardCylinderCoordinates_source_coefficients gX e N hcapture q s p hx.1 hx.2]
  have hlimit := capturedCylinderCoordinates_limit_coefficients g e₀ N hcap₀ q s p hx
  change g.pullbackCoefficients (cylinderNeckChart N q s) x = _ at hlimit
  rw [hlimit]
  rfl





theorem exists_forwardCylinder_metric_error_tail
    {ι : Type*} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold (𝓡 3) ∞ (X i)]
    (gX : ∀ i, RiemannianMetric 3 (X i))
    (e : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X i) ∞) (N : EpsilonNeck g)
    (hcapture : ∀ i, N.carrier ⊆ (e i).source)
    (q : ι → UnitTwoSphere) (s : ι → ℝ) (p : ι → M)
    (hs : ∀ i, s i ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hp : ∀ i, N.coordinate_map (q i, s i) ∈ (extChartAt (𝓡 3) (p i)).source)
    (m : ℕ) (stage : ι → ℕ)
    (hmap : HasUniformJetBoundsAt m
      (fun i => fderiv ℝ ((extChartAt (𝓡 3) (p i)) ∘ cylinderNeckChart N (q i) (s i)))
      (fun _ => 0))
    (herror : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i, K ≤ stage i →
      ∀ r ≤ m, ‖iteratedFDeriv ℝ r
          ((gX i).pullbackCoefficients ((e i) ∘ (extChartAt (𝓡 3) (p i)).symm))
          ((extChartAt (𝓡 3) (p i)) (N.coordinate_map (q i, s i))) -
        iteratedFDeriv ℝ r (g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm)
          ((extChartAt (𝓡 3) (p i)) (N.coordinate_map (q i, s i)))‖ ≤ delta) :
    ∀ rho : ℝ, 0 < rho → ∃ K : ℕ, ∀ i, K ≤ stage i → ∀ r ≤ m,
      ‖iteratedFDeriv ℝ r (fun x =>
        (gX i).pullbackCoefficients ((e i) ∘ cylinderNeckChart N (q i) (s i)) x -
        g.pullbackCoefficients (cylinderNeckChart N (q i) (s i)) x) 0‖ ≤ rho := by
  let e₀ := (Diffeomorph.refl (𝓡 3) M ∞).toPartialDiffeomorph
  have hcap₀ : N.carrier ⊆ e₀.target := fun _ _ => mem_univ _
  let psi := fun i => (extChartAt (𝓡 3) (p i)) ∘ cylinderNeckChart N (q i) (s i)
  let B := fun i => (gX i).pullbackCoefficients ((e i) ∘ (extChartAt (𝓡 3) (p i)).symm)
  let L := fun i => g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm
  have hpsi (i : ι) : ContDiffAt ℝ ∞ (psi i) 0 :=
    (contDiffOn_capturedCylinderCoordinates e₀ N hcap₀ (q i) (s i) (p i)).contDiffAt
      ((isOpen_capturedCylinderChartDomain e₀ N hcap₀ (q i) (s i) (p i)).mem_nhds
        (zero_mem_capturedCylinderChartDomain e₀ N (q i) (hs i) (p i) (hp i)))
  have hzero (i : ι) : psi i 0 =
      (extChartAt (𝓡 3) (p i)) (N.coordinate_map (q i, s i)) := by
    dsimp only [psi, Function.comp_apply]
    rw [cylinderNeckChart_zero]
  have hcinv (i : ι) : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (extChartAt (𝓡 3) (p i)).symm (psi i 0) := by
    apply (contMDiffOn_extChartAt_symm (p i)).contMDiffAt
    apply (isOpen_extChartAt_target (p i)).mem_nhds
    rw [hzero]
    exact (extChartAt (𝓡 3) (p i)).map_source (hp i)
  have hB (i : ι) : ContDiffAt ℝ ∞ (B i) (psi i 0) := by
    apply (gX i).contDiffAt_pullbackCoefficients
    apply ContMDiffAt.comp _ _ (hcinv i)
    apply (e i).contMDiffOn_toFun.contMDiffAt
    apply (e i).open_source.mem_nhds
    rw [hzero, (extChartAt (𝓡 3) (p i)).left_inv (hp i)]
    exact hcapture i (N.coordinate_map_mem_of_axial _ (hs i))
  have hL (i : ι) : ContDiffAt ℝ ∞ (L i) (psi i 0) :=
    g.contDiffAt_pullbackCoefficients (hcinv i)
  have hE : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i, K ≤ stage i →
      ∀ r ≤ m, ‖iteratedFDeriv ℝ r (fun y => B i y - L i y) (psi i 0)‖ ≤ delta := by
    intro delta hdelta
    obtain ⟨K, hK⟩ := herror delta hdelta
    refine ⟨K, fun i hi r hr => ?_⟩
    change ‖iteratedFDeriv ℝ r (B i - L i) (psi i 0)‖ ≤ delta
    rw [iteratedFDeriv_sub_apply
      ((hB i).of_le (by exact_mod_cast le_top))
      ((hL i).of_le (by exact_mod_cast le_top)), hzero]
    exact hK i hi r hr
  have htail := exists_bilinear_pullback_error_tail m stage hmap hpsi
    (fun i => (hB i).sub (hL i)) hE
  intro rho hrho
  obtain ⟨K, hK⟩ := htail rho hrho
  refine ⟨K, fun i hi r hr => ?_⟩
  rw [((forwardCylinderCoordinates_error_germ (gX i) (e i) N (hcapture i)
    (q i) (p i) (hs i) (hp i)).iteratedFDeriv ℝ r).eq_of_nhds]
  exact hK i hi r hr

end PoincareConjecture.Proofs.M28.NeckTransfer
