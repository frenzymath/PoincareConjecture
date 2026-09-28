import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Heat.Dirichlet.Resolvent

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem integral_mul_laplacian_of_compact_test {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (hfc : HasCompactSupport f) :
    (∫ x, f x * D.laplacian h x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient f x) (D.gradient h x) ∂g.volumeMeasure) := by
  classical
  let b : ∀ x : tsupport f, SmoothBumpFunction (𝓡 n) (x : M) :=
    fun x => Classical.choice inferInstance
  let U (x : tsupport f) : Set M := interior {y | b x y = 1}
  have hcover : tsupport f ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_interior_iff_mem_nhds.mpr (b ⟨x, hx⟩).eventuallyEq_one⟩
  obtain ⟨s, hs⟩ := hfc.isCompact.elim_finite_subcover U (fun _ => isOpen_interior) hcover
  let B : SmoothBumpCovering s (𝓡 n) M (tsupport f) :=
    { c := fun i => i.val.val
      toFun := fun i => b i.val
      c_mem' := fun i => i.val.property
      locallyFinite' := locallyFinite_of_finite _
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
        exact ⟨⟨i, his⟩, mem_of_superset (isOpen_interior.mem_nhds hxi) interior_subset⟩ }
  let ρ := B.toSmoothPartitionOfUnity
  let w : s → M → ℝ := fun i x => ρ i x * f x
  have hw (i : s) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w i) :=
    (ρ i).contMDiff.mul hf
  have hwc (i : s) : HasCompactSupport (w i) := hfc.mul_left
  have hws (i : s) : tsupport (w i) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) i.val.val).source := by
    apply tsupport_mul_subset_left.trans
    exact (closure_mono (B.support_toSmoothPartitionOfUnity_subset i)).trans
      (b i.val).tsupport_subset_chartAt_source
  have hsum (x : M) : ∑ i : s, w i x = f x := by
    by_cases hx : x ∈ tsupport f
    · have hp := ρ.sum_eq_one hx
      simpa only [w, ← Finset.sum_mul, finsum_eq_sum_of_fintype, hp, one_mul] using
        congrArg (fun z : ℝ => z * f x) hp
    · simp [w, image_eq_zero_of_notMem_tsupport hx]
  have hgrad (x : M) : D.gradient f x = ∑ i : s, D.gradient (w i) x := by
    conv_lhs => rw [← funext hsum]
    exact D.gradient_finset_sum Finset.univ w x
      (fun i _ => (hw i x).mdifferentiableAt (by simp))
  have hlocal (i : s) := D.integral_mul_laplacian_of_tsupport_subset_chart
    (chartAt (EuclideanSpace ℝ (Fin n)) i.val.val).symm
    contMDiffOn_chart_symm contMDiffOn_chart (hw i) hh (hwc i) (hws i)
  calc
    _ = ∫ x, ∑ i : s, w i x * D.laplacian h x ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_mul, hsum]
    _ = ∑ i : s, ∫ x, w i x * D.laplacian h x ∂g.volumeMeasure :=
      integral_finsetSum _ (fun i _ => D.integrable_mul_laplacian (hw i) hh (hwc i))
    _ = -(∑ i : s, ∫ x, g.inner x (D.gradient (w i) x) (D.gradient h x)
        ∂g.volumeMeasure) := by simp only [hlocal, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i : s, g.inner x (D.gradient (w i) x) (D.gradient h x)
        ∂g.volumeMeasure) := by
      rw [integral_finsetSum _ (fun i _ => D.integrable_inner_gradient (hw i) hh (hwc i))]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [hgrad, map_sum, sum_apply]

theorem exists_energyTest_approximation (u : H1Zero D Ω) :
    ∃ f : ℕ → EnergyTest D Ω,
      Tendsto (fun k => (f k : H1Zero D Ω)) atTop (𝓝 u) ∧
      Tendsto (fun k => testToL2 D Ω (f k)) atTop (𝓝 (toL2 D Ω u)) := by
  have hd : u ∈ closure (range (fun f : EnergyTest D Ω => (f : H1Zero D Ω))) := by
    rw [Completion.denseRange_coe.closure_eq]
    exact mem_univ _
  obtain ⟨s, hs, hsu⟩ := mem_closure_iff_seq_limit.mp hd
  choose f hf using hs
  have hfu : Tendsto (fun k => (f k : H1Zero D Ω)) atTop (𝓝 u) := by
    simpa only [hf] using hsu
  exact ⟨f, hfu, by
    simpa only [Function.comp_def, toL2_coe] using
      (toL2 D Ω).continuous.continuousAt.tendsto.comp hfu⟩

theorem energyInner_eq_integral_oneSubLaplacian_of_compact_test
    (f h : EnergyTest D Ω) :
    energyInner f h = ∫ x, (f x - D.laplacian f x) * h x ∂g.volumeMeasure := by
  have hgreen := integral_mul_laplacian_of_compact_test (D := D)
    h.smooth f.smooth h.hasCompactSupport
  have heq : (fun x => (f x - D.laplacian f x) * h x) =
      fun x => h x * f x - h x * D.laplacian f x := by funext x; ring
  rw [heq, integral_sub (h.integrable_mul f)
    (D.integrable_mul_laplacian h.smooth f.smooth h.hasCompactSupport), hgreen,
    energyInner_symm f h]
  simp only [energyInner, sub_neg_eq_add]

theorem inner_test_eq_oneSubLaplacian (f : EnergyTest D Ω)
    (u : H1Zero D Ω) :
    ⟪(f : H1Zero D Ω), u⟫_ℝ = ⟪f.oneSubLaplacian, toL2 D Ω u⟫_ℝ := by
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (toL2 D Ω).continuous)
  | ih h =>
    rw [Completion.inner_coe, EnergyTest.inner_eq, toL2_coe,
      energyInner_eq_integral_oneSubLaplacian_of_compact_test, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [f.oneSubLaplacian_memLp.coeFn_toLp, h.memLp.coeFn_toLp] with x hfx hhx
    change (f x - D.laplacian f x) * h x =
      inner ℝ (f.oneSubLaplacian x) ((testToL2 D Ω h) x)
    rw [show f.oneSubLaplacian x = f x - D.laplacian f x from hfx,
      show (testToL2 D Ω h) x = h x from hhx]
    simp [mul_comm]

theorem weakEigen_oneSubLaplacian_test
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    (f : EnergyTest D Ω) :
    ⟪f.oneSubLaplacian, toL2 D Ω u⟫_ℝ =
    (1 + lambda) * ⟪toL2 D Ω u, testToL2 D Ω f⟫_ℝ := by
  rw [← inner_test_eq_oneSubLaplacian f u]
  rw [real_inner_comm]
  rw [heigen]
  rw [toL2_coe]

theorem EnergyTest.laplacian_memLp (f : EnergyTest D Ω) :
    MemLp (D.laplacian f) 2 g.volumeMeasure :=
  (D.continuous_laplacian f.smooth).memLp_of_hasCompactSupport
    (D.hasCompactSupport_laplacian f.hasCompactSupport)

theorem integral_test_mul (v : Lp ℝ 2 g.volumeMeasure) (f : EnergyTest D Ω) :
    (∫ x, f x * v x ∂g.volumeMeasure) = ⟪v, testToL2 D Ω f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.memLp.coeFn_toLp] with x hx
  change f x * v x = inner ℝ (v x) ((testToL2 D Ω f) x)
  rw [show (testToL2 D Ω f) x = f x from hx]
  simp

theorem weakEigen_integral_laplacian_test
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    (f : EnergyTest D Ω) :
    (∫ x, D.laplacian f x * (toL2 D Ω u) x ∂g.volumeMeasure) =
      -lambda * ∫ x, f x * (toL2 D Ω u) x ∂g.volumeMeasure := by
  have h := weakEigen_oneSubLaplacian_test u lambda heigen f
  have hleft : ⟪f.oneSubLaplacian, toL2 D Ω u⟫_ℝ =
      (∫ x, f x * (toL2 D Ω u) x ∂g.volumeMeasure) -
        ∫ x, D.laplacian f x * (toL2 D Ω u) x ∂g.volumeMeasure := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℝ (f.oneSubLaplacian x) ((toL2 D Ω u) x) ∂g.volumeMeasure) =
          ∫ x, (f x - D.laplacian f x) * (toL2 D Ω u) x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [f.oneSubLaplacian_memLp.coeFn_toLp] with x hx
        rw [show f.oneSubLaplacian x = f x - D.laplacian f x from hx]
        simp [mul_comm]
      _ = _ := by
        have h₁ := f.memLp.integrable_mul (Lp.memLp (toL2 D Ω u))
        have h₂ := f.laplacian_memLp.integrable_mul (Lp.memLp (toL2 D Ω u))
        simpa only [Pi.mul_apply, sub_mul] using integral_sub h₁ h₂
  rw [hleft, ← integral_test_mul] at h
  linarith

end PoincareConjecture.LeviCivitaData.Dirichlet
