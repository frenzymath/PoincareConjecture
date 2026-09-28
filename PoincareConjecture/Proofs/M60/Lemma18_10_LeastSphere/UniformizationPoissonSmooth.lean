import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationPoissonCoordinates
import PoincareConjecture.Proofs.M60.Mathlib.UniformizationEllipticRegularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace

universe u

namespace PoincareConjecture.M60

open LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}




theorem exists_smooth_poisson_representative (hn : 0 < n)
    {Omega : Set M} (hOmega : IsOpen Omega)
    (u : H1Zero D Omega) (F : Lp ℝ 2 g.volumeMeasure)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hF : (F : M → ℝ) =ᵐ[g.volumeMeasure] f)
    (hforce : ∀ v : H1Zero D Omega,
      ⟪u, v⟫_ℝ - ⟪toL2 D Omega u, toL2 D Omega v⟫_ℝ = ⟪F, toL2 D Omega v⟫_ℝ) :
    ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Omega ∧
      U =ᵐ[g.volumeMeasure.restrict Omega] (toL2 D Omega u : M → ℝ) := by
  apply exists_smooth_representative_of_local hOmega (toL2 D Omega u)
  intro x hx
  obtain ⟨e, he, hei, K, hK, hKs, O, hO, hOK, hxO, hOOmega, -⟩ :=
    exists_precompact_coordinate_neighborhood (n := n) hOmega hx
  have hOs := hOK.trans hKs
  let p (i : Fin n) := localCoordinateDerivative (D := D) (Ω := Omega)
    e he hei hK hKs hOK (EuclideanSpace.single i 1) u
  have huL2 : MemLp (fun y => toL2 D Omega u (e y)) 2 (volume.restrict O) :=
    (g.memLp_pullback_on_compact e he hei (toL2 D Omega u) hK hKs).mono_measure
      (Measure.restrict_mono hOK le_rfl)
  have hpL2 (i : Fin n) : MemLp (p i) 2 (volume.restrict O) := Lp.memLp (p i)
  have hweak (i : Fin n) (phi : EuclideanSpace ℝ (Fin n) → ℝ)
      (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) :
      (∫ y in O, toL2 D Omega u (e y) * fderiv ℝ phi y (EuclideanSpace.single i 1)) =
        -(∫ y in O, p i y * phi y) :=
    localCoordinateDerivative_weak e he hei hK hKs hOK hO u i hphi hc hs
  have hdiv (phi : EuclideanSpace ℝ (Fin n) → ℝ)
      (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) :
      (∫ y in O, ∑ i, ∑ j, divergenceCoefficients g e y i j * p j y *
        fderiv ℝ phi y (EuclideanSpace.single i 1)) =
        ∫ y in O, (g.pullbackVolumeDensity e y * f (e y)) * phi y := by
    rw [weakPoisson_divergence_local e he hei hK hKs hOK hOOmega u F hforce hphi hc hs]
    have hFc := (g.ae_comp_on_compact e he hei hK hKs hF).filter_mono
      (ae_mono (Measure.restrict_mono hOK le_rfl))
    apply integral_congr_ae
    filter_upwards [hFc] with y hy
    rw [hy]
  obtain ⟨V, hVs, hVae⟩ : ∃ V : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ V O ∧ V =ᵐ[volume.restrict O] (fun y => toL2 D Omega u (e y)) := by
    apply exists_smooth_representative_of_smooth_forcing hn hO
      (divergenceCoefficients g e) (fun y => g.pullbackVolumeDensity e y * f (e y))
      (fun y => toL2 D Omega u (e y)) (fun i y => p i y)
    · intro i j
      exact (contDiffOn_divergenceCoefficients e he hei i j).mono hOs
    · intro y hy
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        change divergenceCoefficients g e y j i = divergenceCoefficients g e y i j
        exact divergenceCoefficients_symm e he hei (hOs hy) j i
      · intro v hv
        have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
          intro hz
          exact hv (congrArg WithLp.ofLp hz)
        have hpos := divergenceCoefficients_pos (g := g) e he hei (hOs hy)
          (WithLp.toLp 2 v) hv'
        simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
          Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
    · apply ContDiffOn.mul ?_ ((hf.comp_contMDiffOn he).contDiffOn.mono hOs)
      intro y hy
      have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
        ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
      exact (g.contDiffAt_pullbackVolumeDensity
        (he.contMDiffAt (e.open_source.mem_nhds (hOs hy)))
        (hD.mfderiv_injective (hOs hy))).1.contDiffWithinAt
    · intro C _ hCO
      exact huL2.mono_measure (Measure.restrict_mono hCO le_rfl)
    · intro i C _ hCO
      exact (hpL2 i).mono_measure (Measure.restrict_mono hCO le_rfl)
    · exact hweak
    · exact hdiv
  obtain ⟨H, hHs, hHae⟩ := g.exists_smooth_representative_on_coordinate_image
    e he hei hO hOs (toL2 D Omega u) hVs hVae
  exact ⟨e '' O, e.isOpen_image_of_subset_source hO hOs, hxO, hOOmega, H, hHs, hHae⟩




theorem laplacian_eq_of_closed_smooth_poisson [CompactSpace M]
    (u : H1Zero D univ) (F : Lp ℝ 2 g.volumeMeasure)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hF : (F : M → ℝ) =ᵐ[g.volumeMeasure] f)
    (hforce : ∀ v : H1Zero D univ,
      ⟪u, v⟫_ℝ - ⟪toL2 D univ u, toL2 D univ v⟫_ℝ = ⟪F, toL2 D univ v⟫_ℝ)
    {U : M → ℝ} (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U)
    (hUae : U =ᵐ[g.volumeMeasure] (toL2 D univ u : M → ℝ)) :
    ∀ x, -D.laplacian U x = f x := by
  let R := fun x => D.laplacian U x + f x
  have hR : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R := (D.contMDiff_laplacian hU).add hf
  let r : EnergyTest D univ :=
    ⟨R, hR, HasCompactSupport.of_compactSpace _, subset_univ _⟩
  have hdom : (toDomainL2 D univ u : M → ℝ) =ᵐ[g.volumeMeasure] U := by
    have h := toDomainL2_ae u
    simp only [Measure.restrict_univ] at h
    exact h.trans hUae.symm
  have henergy := inner_energy_test_eq_domain_integral (MeasurableSet.univ : MeasurableSet
    (univ : Set M)) u r
  simp only [setIntegral_univ] at henergy
  have henergy' : ⟪u, (r : H1Zero D univ)⟫_ℝ =
      (∫ x, r x * U x ∂g.volumeMeasure) -
        ∫ x, D.laplacian r x * U x ∂g.volumeMeasure := by
    rw [henergy]
    calc
      _ = ∫ x, (r x - D.laplacian r x) * U x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [hdom] with x hx
        rw [hx]
      _ = _ := by
        have h1 : Integrable (fun x => r x * U x) g.volumeMeasure :=
          (r.smooth.continuous.mul hU.continuous).integrable_of_hasCompactSupport
            r.hasCompactSupport.mul_right
        have h2 : Integrable (fun x => D.laplacian r x * U x) g.volumeMeasure :=
          ((D.continuous_laplacian r.smooth).mul hU.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        simpa only [Pi.mul_apply, sub_mul] using integral_sub h1 h2
  have hpair := hforce (r : H1Zero D univ)
  rw [henergy', toL2_coe, ← integral_test_mul, ← integral_test_mul] at hpair
  have htestU : (∫ x, r x * toL2 D univ u x ∂g.volumeMeasure) =
      ∫ x, r x * U x ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [hUae] with x hx
    rw [hx]
  have htestF : (∫ x, r x * F x ∂g.volumeMeasure) =
      ∫ x, r x * f x ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]
  rw [htestU, htestF] at hpair
  have hgreen := integral_mul_laplacian_comm_of_compact_tests (D := D)
    r.smooth hU r.hasCompactSupport (HasCompactSupport.of_compactSpace U)
  have hcomm : (∫ x, U x * D.laplacian r x ∂g.volumeMeasure) =
      ∫ x, D.laplacian r x * U x ∂g.volumeMeasure := by
    congr 1
    funext x
    ring
  rw [hcomm] at hgreen
  have hzero : (∫ x, R x * R x ∂g.volumeMeasure) = 0 := by
    calc
      _ = ∫ x, r x * D.laplacian U x + r x * f x ∂g.volumeMeasure := by
        congr 1
        funext x
        change R x * R x = R x * D.laplacian U x + R x * f x
        dsimp only [R]
        ring
      _ = (∫ x, r x * D.laplacian U x ∂g.volumeMeasure) +
          ∫ x, r x * f x ∂g.volumeMeasure := by
        apply integral_add
        · exact Continuous.integrable_of_hasCompactSupport
            (r.smooth.continuous.mul (D.continuous_laplacian hU)) r.hasCompactSupport.mul_right
        · exact (r.smooth.continuous.mul hf.continuous).integrable_of_hasCompactSupport
            r.hasCompactSupport.mul_right
      _ = 0 := by rw [hgreen]; linarith
  intro x
  have hRx : R x = 0 := by
    by_contra hRx
    let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
    have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := g.volumeMeasure)
      (hR.continuous.mul hR.continuous)
      ((hR.continuous.mul hR.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (fun y => mul_self_nonneg (R y)) (x := x) (mul_ne_zero hRx hRx)
    exact hpos.ne' hzero
  change D.laplacian U x + f x = 0 at hRx
  linarith

end PoincareConjecture.M60
