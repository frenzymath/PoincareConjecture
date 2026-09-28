import PoincareConjecture.Proofs.M30.Thm11_1.CapturedNeckTransferBounds
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CapturedCylinderErrors
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.Comparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M30.CapturedNeckTransfer

open PoincareConjecture.M28.tube PoincareConjecture.Proofs.M28.NeckTransfer
open PoincareConjecture.Proofs.M28.NeckAnalysis PoincareConjecture.Proofs.M28.FiniteHessian

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {X : ℕ → Type u} [∀ k, TopologicalSpace (X k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X k)]
  [∀ k, IsManifold (𝓡 3) ∞ (X k)] {ι : Type w} [Finite ι]

theorem exists_metric_error_tail
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (X k))
    (e : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X k) ∞)
    (N : ∀ k, EpsilonNeck (h k)) {epsilon eta : ℝ}
    (hepsilon : 0 < epsilon) (hepseta : epsilon ≤ eta) (heta : eta < 1 / 2)
    (heps : ∀ k, (N k).epsilon = epsilon)
    {U K : Set M} (hsource : ∀ k, (e k).source = U) (hKU : K ⊆ U)
    (hcapture : ∀ k, (N k).carrier ⊆ (e k) '' K)
    {amin B : ℝ} (hamin : 0 < amin)
    (hscale : ∀ k, amin ≤ (N k).scale ^ 2 ∧ (N k).scale ^ 2 ≤ B)
    (q : ι → M) (L : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hL : ∀ i, IsCompact (L i))
    (htarget : ∀ i, L i ⊆ (extChartAt (𝓡 3) (q i)).target)
    (hcover : K ⊆ ⋃ i, (extChartAt (𝓡 3) (q i)).symm '' L i)
    (m : ℕ) (hm : m + 1 ≤ ⌊epsilon⁻¹⌋₊)
    (hjets : ∀ i r, r ≤ m + 1 → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        ((h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm)))
      (iteratedFDeriv ℝ r (g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
      atTop (L i)) :
    ∀ rho : ℝ, 0 < rho → ∃ K0 : ℕ, ∀ k ≥ K0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ → ∀ r ≤ m,
        ‖iteratedFDeriv ℝ r (fun x =>
          g.pullbackCoefficients (capturedCylinderMap (e k) (N k) z.1 z.2) x -
          (h k).pullbackCoefficients (cylinderNeckChart (N k) z.1 z.2) x) 0‖ ≤ rho := by
  classical
  have hcap (k : ℕ) : (N k).carrier ⊆ (e k).target := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hcapture k hx
    exact (e k).map_source (by rw [hsource]; exact hKU hy)
  have hinv (k : ℕ) {x : X k} (hx : x ∈ (N k).carrier) : (e k).symm x ∈ K := by
    obtain ⟨y, hy, rfl⟩ := hcapture k hx
    have hxy : (e k).symm (e k y) = y :=
      (e k).left_inv (by rw [hsource]; exact hKU hy)
    exact hxy.symm ▸ hy
  obtain ⟨c, B0, hc, _, hbounds⟩ :=
    exists_eventual_atlas_bounds g h e q L hL htarget (m + 1) hjets
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hbounds
  let J := {z : ℕ × RoundCylinderSpace × ι // K0 ≤ z.1 ∧
    z.2.1.2 ∈ Ioo (-eta⁻¹) eta⁻¹ ∧
    (e z.1).symm ((N z.1).coordinate_map z.2.1) ∈
      (extChartAt (𝓡 3) (q z.2.2)).symm '' L z.2.2}
  let y := fun i : J => capturedCylinderCoordinates (e i.1.1) (N i.1.1)
    i.1.2.1.1 i.1.2.1.2 (q i.1.2.2) 0
  have hy (i : J) : y i ∈ L i.1.2.2 := by
    change (extChartAt (𝓡 3) (q i.1.2.2))
      ((e i.1.1).symm (cylinderNeckChart (N i.1.1) i.1.2.1.1 i.1.2.1.2 0)) ∈ _
    rw [cylinderNeckChart_zero]
    obtain ⟨z, hz, heq⟩ := i.2.2.2
    rw [← heq, (extChartAt (𝓡 3) (q i.1.2.2)).right_inv (htarget _ hz)]
    exact hz
  have hp (i : J) : (e i.1.1).symm ((N i.1.1).coordinate_map i.1.2.1) ∈
      (extChartAt (𝓡 3) (q i.1.2.2)).source := by
    obtain ⟨z, hz, heq⟩ := i.2.2.2
    rw [← heq]
    exact (extChartAt (𝓡 3) (q i.1.2.2)).map_target (htarget _ hz)
  have hs (i : J) : i.1.2.1.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    cylinderStrip_mono hepsilon hepseta i.2.2.1
  have hsN (i : J) : i.1.2.1.2 ∈
      Ioo (-(N i.1.1).epsilon⁻¹) (N i.1.1).epsilon⁻¹ := by
    simpa only [heps] using hs i
  have hAj := source_coefficient_jets (fun i : J => N i.1.1)
    hepsilon (by linarith) (fun i => heps i.1.1) (fun i => (hscale i.1.1).2)
    (fun i => i.1.2.1.1) (fun i => i.1.2.1.2) hs (m + 1) hm
  have hBj : HasUniformJetBoundsAt (m + 1)
      (fun i : J => (h i.1.1).pullbackCoefficients
        (e i.1.1 ∘ (extChartAt (𝓡 3) (q i.1.2.2)).symm)) y := by
    intro r hr
    exact ⟨B0, fun i => (hK0 i.1.1 i.2.1 i.1.2.2 (y i) (hy i)).2 r hr⟩
  have hsourcepos : 0 < amin * (1 - epsilon) := mul_pos hamin (by linarith)
  have hAe (i : J) (v : EuclideanSpace ℝ (Fin 3)) :
      (amin * (1 - epsilon)) * ‖v‖ ^ 2 ≤
        (h i.1.1).pullbackCoefficients
          (cylinderNeckChart (N i.1.1) i.1.2.1.1 i.1.2.1.2) 0 v v := by
    rw [cylinderNeckCoefficients_unscale]
    change _ ≤ (N i.1.1).scale ^ 2 *
      cylinderNeckCoefficients (N i.1.1) i.1.2.1.1 i.1.2.1.2 0 v v
    have hlow := (cylinderNeckCoefficients_quadratic_bounds
      (N i.1.1) i.1.2.1.1 (hsN i) v).1
    rw [heps] at hlow
    calc
      _ = amin * ((1 - epsilon) * ‖v‖ ^ 2) := by ring
      _ ≤ (N i.1.1).scale ^ 2 * ((1 - epsilon) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hscale i.1.1).1
          (mul_nonneg (by linarith) (sq_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
  have hmap := hasUniformJetBoundsAt_capturedCylinderCoordinates_fderiv
    (fun i : J => h i.1.1) (fun i => e i.1.1) (fun i => N i.1.1)
    (fun i => hcap i.1.1) (fun i => i.1.2.1.1) (fun i => i.1.2.1.2)
    (fun i => q i.1.2.2) hsN hp m hAj hBj hsourcepos hc hAe
    (fun i v => (hK0 i.1.1 i.2.1 i.1.2.2 (y i) (hy i)).1 v)
  have herror : ∀ delta : ℝ, 0 < delta → ∃ K1 : ℕ, ∀ i : J, K1 ≤ i.1.1 →
      ∀ r ≤ m, ‖iteratedFDeriv ℝ r
          ((h i.1.1).pullbackCoefficients
            (e i.1.1 ∘ (extChartAt (𝓡 3) (q i.1.2.2)).symm)) (y i) -
        iteratedFDeriv ℝ r
          (g.pullbackCoefficients (extChartAt (𝓡 3) (q i.1.2.2)).symm) (y i)‖ ≤ delta := by
    intro delta hdelta
    have hall := Filter.eventually_all.mpr (fun i : ι × Fin (m + 1) =>
      Metric.tendstoUniformlyOn_iff.mp (hjets i.1 i.2 (by omega)) delta hdelta)
    obtain ⟨K1, hK1⟩ := eventually_atTop.mp hall
    refine ⟨K1, ?_⟩
    intro i hi r hr
    have hh := hK1 i.1.1 hi (i.1.2.2, ⟨r, Nat.lt_succ_of_le hr⟩) (y i) (hy i)
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hh)
  have hmap' : HasUniformJetBoundsAt m
      (fun i : J => fderiv ℝ (capturedCylinderCoordinates (e i.1.1) (N i.1.1)
        i.1.2.1.1 i.1.2.1.2 (q i.1.2.2))) (fun _ => 0) :=
    fun r hr => hmap r (hr.trans (Nat.le_succ m))
  have htail := exists_capturedCylinder_metric_error_tail g
    (fun i : J => h i.1.1) (fun i => e i.1.1) (fun i => N i.1.1)
    (fun i => hcap i.1.1) (fun i => i.1.2.1.1) (fun i => i.1.2.1.2)
    (fun i => q i.1.2.2) hsN hp m (fun i => i.1.1) hmap' herror
  intro rho hrho
  obtain ⟨K1, hK1⟩ := htail rho hrho
  refine ⟨max K0 K1, ?_⟩
  intro k hk z hz r hr
  have hk0 : K0 ≤ k := (le_max_left _ _).trans hk
  have hzN : z.2 ∈ Ioo (-(N k).epsilon⁻¹) (N k).epsilon⁻¹ := by
    rw [heps]
    exact cylinderStrip_mono hepsilon hepseta hz
  have hzK := hinv k ((N k).coordinate_map_mem_of_axial z hzN)
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hzK)
  let j : J := ⟨(k, z, i), hk0, hz, hi⟩
  exact hK1 j ((le_max_right _ _).trans hk) r hr

end PoincareConjecture.M30.CapturedNeckTransfer
