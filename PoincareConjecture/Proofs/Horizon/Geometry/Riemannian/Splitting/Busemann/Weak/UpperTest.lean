import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Weak.Comparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem laplacian_upper_test_nonneg_of_compact_comparison (D : LeviCivitaData g)
    {u : M → ℝ}
    (hcompare : ∀ (K : Set M), IsCompact K → ∀ φ : M → ℝ,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ →
      (∀ x ∈ K, D.laplacian φ x < 0) →
      (∀ x ∈ K, x ∉ interior K → u x ≤ φ x) → ∀ x ∈ K, u x ≤ φ x)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    {x : M} (hmax : IsLocalMax (fun y => u y - φ y) x) :
    0 ≤ D.laplacian φ x := by
  by_contra hfail
  have hneg : D.laplacian φ x < 0 := lt_of_not_ge hfail
  have hneighborhood : ∀ᶠ y in 𝓝 x, D.laplacian φ y < 0 :=
    (D.continuous_laplacian hφ).continuousAt.eventually (Iio_mem_nhds hneg)
  obtain ⟨χ, _, hχsub⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
      (inter_mem hmax hneighborhood)
  have hxK : x ∈ tsupport (χ : M → ℝ) := subset_closure χ.c_mem_support
  obtain ⟨q, hq, hqmax⟩ := χ.hasCompactSupport.isCompact.exists_isMaxOn ⟨x, hxK⟩
    (D.continuous_laplacian hφ).continuousOn
  have hqneg := (hχsub hq).2
  change D.laplacian φ q < 0 at hqneg
  obtain ⟨C₀, hC₀⟩ := χ.hasCompactSupport.isCompact.bddAbove_image
    (D.continuous_laplacian χ.contMDiff).abs.continuousOn
  let C := max 1 C₀
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let A := -(D.laplacian φ q) / 2
  have hA : 0 < A := by dsimp [A]; linarith
  let δ := A / C
  have hδ : 0 < δ := div_pos hA hC
  have hδC : δ * C = A := div_mul_cancel₀ _ hC.ne'
  let ψ := fun y => (u x - φ x) + φ y - δ * χ y
  have hshift : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (u x - φ x) + φ y) := contMDiff_const.add hφ
  have hscale : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => δ * χ y) := contMDiff_const.mul χ.contMDiff
  have hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ :=
    hshift.sub hscale
  have hψlap : ∀ y ∈ tsupport (χ : M → ℝ), D.laplacian ψ y < 0 := by
    intro y hy
    have hχbound : |D.laplacian (χ : M → ℝ) y| ≤ C :=
      (hC₀ (mem_image_of_mem _ hy)).trans (le_max_right _ _)
    have hlower : -C ≤ D.laplacian (χ : M → ℝ) y := (abs_le.mp hχbound).1
    have hmul := mul_le_mul_of_nonneg_left hlower hδ.le
    have hφbound := hqmax hy
    change D.laplacian φ y ≤ D.laplacian φ q at hφbound
    change D.laplacian (fun z => (u x - φ x) + φ z - δ * χ z) y < 0
    rw [D.laplacian_sub hshift hscale, D.laplacian_const_add_at (hφ y),
      D.laplacian_const_mul]
    dsimp [A] at hδC
    nlinarith
  have hboundary : ∀ y ∈ tsupport (χ : M → ℝ),
      y ∉ interior (tsupport (χ : M → ℝ)) → u y ≤ ψ y := by
    intro y hy hnot
    have hzero : χ y = 0 := by
      by_contra hne
      have hs : y ∈ Function.support (χ : M → ℝ) := hne
      exact hnot (interior_maximal subset_closure χ.isOpen_support hs)
    have hcontact := (hχsub hy).1
    change u y - φ y ≤ u x - φ x at hcontact
    dsimp [ψ]
    rw [hzero, mul_zero, sub_zero]
    linarith
  have h := hcompare _ χ.hasCompactSupport.isCompact ψ hψ hψlap hboundary x hxK
  dsimp [ψ] at h
  rw [χ.eq_one] at h
  linarith

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

theorem busemann_laplacian_upper_test_nonneg
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    {x : M} (hmax : IsLocalMax (fun y => g.busemann γ y - φ y) x) :
    0 ≤ D.laplacian φ x := by
  apply D.laplacian_upper_test_nonneg_of_compact_comparison (u := g.busemann γ)
    (fun K hK φ hφ hlap hboundary =>
      g.busemann_le_on_compact_of_laplacian_neg D hm hcomplete hRic hγ hK hφ hlap hboundary)
    hφ hmax

theorem busemann_add_reverse_laplacian_upper_test_nonneg
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    {x : M}
    (hmax : IsLocalMax
      (fun y => g.busemann γ y + g.busemann (fun s => γ (-s)) y - φ y) x) :
    0 ≤ D.laplacian φ x := by
  apply D.laplacian_upper_test_nonneg_of_compact_comparison
    (u := fun y => g.busemann γ y + g.busemann (fun s => γ (-s)) y)
    (fun K hK φ hφ hlap hboundary =>
      g.busemann_add_reverse_le_on_compact_of_laplacian_neg D hm hcomplete hRic
        hγ hK hφ hlap hboundary) hφ hmax

end PoincareConjecture.RiemannianMetric
