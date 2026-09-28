import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.WeakEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Charts
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.NormalDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.LocalTangentialRegularity
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.LocalEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.VariationalEquation







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

open Poincare.Analysis.Sobolev

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

local notation "E" => EuclideanSpace ℝ (Fin n)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_chart_cutoff_elliptic
    (g : RiemannianMetric n M) (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (W : Set E)
      (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ),
      (x : M) ∈ e.target ∧ e.symm x ∈ W ∧ IsOpen W ∧
      IsCompact (closure W) ∧ closure W ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ W, χ (e z) = 1) ∧
      EqOn B.a (divergenceCoefficients g e) W := by
  obtain ⟨e, U, hx, hxU, hU, _, hUs, he, hei, hflat, hB⟩ :=
    exists_local_elliptic_form g S x
  obtain ⟨B, hBA, _⟩ := hB 0
  obtain ⟨χ, _, hχs⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) (x : M)).mem_iff.mp
    (e.open_target.mem_nhds hx)
  have heAt : ContinuousAt e (e.symm x) := e.continuousAt (e.map_target hx)
  have heLim : Tendsto e (𝓝 (e.symm x)) (𝓝 (x : M)) := by
    simpa only [e.right_inv hx] using heAt.tendsto
  have hχe : (fun z => χ (e z)) =ᶠ[𝓝 (e.symm x)] 1 := χ.eventuallyEq_one.comp_tendsto heLim
  obtain ⟨T, hTsub, hT, hxT⟩ := mem_nhds_iff.mp hχe
  obtain ⟨W, hW, hxW, hWUT, hWc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) (hU.inter hT) (singleton_subset_iff.mpr ⟨hxU, hxT⟩)
  have hWU : W ⊆ U := subset_closure.trans (hWUT.trans inter_subset_left)
  exact ⟨e, χ, W, B, hx, hxW (mem_singleton _), hW, hWc,
    (hWUT.trans inter_subset_left).trans (subset_closure.trans hUs), he, hei, hflat,
    χ.contMDiff, χ.hasCompactSupport, hχs,
    fun z hz => hTsub ((hWUT (subset_closure hz)).2), hBA.mono hWU⟩

private theorem weakEquation_with_elliptic_extension
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ)
    {W : Set E} (hW : IsOpen W) {A : E → Matrix (Fin n) (Fin n) ℝ}
    (hBA : EqOn B.a A W) {p : Fin n → E → ℝ} {f : E → ℝ}
    (hF : ∀ i, MemLp (fun z => ∑ j, A z i j * p j z)
      2 (volume.restrict (W ∩ {z : E | 0 < z 0})))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ {z : E | 0 < z 0} →
      (∫ z in W ∩ {z : E | 0 < z 0}, ∑ i, ∑ j, A z i j * p j z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      ∫ z in W ∩ {z : E | 0 < z 0}, f z * φ z) :
    (∀ j, MemLp (fun z => ∑ i, B.a z i j * p i z)
      2 (volume.restrict (W ∩ {z : E | 0 < z 0}))) ∧
    (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ {z : E | 0 < z 0} →
      (∫ z in W ∩ {z : E | 0 < z 0}, ∑ j, (∑ i, B.a z i j * p i z) *
        fderiv ℝ φ z (EuclideanSpace.single j 1)) =
      ∫ z in W ∩ {z : E | 0 < z 0}, f z * φ z) := by
  have hH : IsOpen {z : E | 0 < z 0} := isOpen_lt continuous_const (by fun_prop)
  have hflux (j : Fin n) {z : E} (hz : z ∈ W) :
      (∑ i, B.a z i j * p i z) = ∑ i, A z j i * p i z := by
    apply Finset.sum_congr rfl
    intro i _
    rw [B.symm z i j, hBA hz]
  constructor
  · intro j
    apply (hF j).ae_eq
    filter_upwards [ae_restrict_mem (hW.inter hH).measurableSet] with z hz
    exact (hflux j hz.1).symm
  · intro φ hφ hc hs
    rw [← heq φ hφ hc hs]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hW.inter hH).measurableSet] with z hz
    simp only [hflux _ hz.1, Finset.sum_mul]

omit [NeZero n] in
private theorem memLp_compact_coeff_mul {K O : Set E} (hK : IsCompact K)
    (hO : MeasurableSet O) (hOK : O ⊆ K) {a v : E → ℝ}
    (ha : ContinuousOn a K) (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun z => a z * v z) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha
  apply hv.of_le_mul (((ha.mono hOK).aestronglyMeasurable hO).mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hO] with z hz
  change ‖a z * v z‖ ≤ C * ‖v z‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC z (hOK hz)) (norm_nonneg _)



theorem weakSolution_localized_divergence
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWs : closure W ⊆ e.source) (hone : ∀ z ∈ W, χ (e z) = 1)
    (u : H1Zero D Ω) (f : Lp ℝ 2 g.volumeMeasure)
    (hsol : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ) :
    let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
    let H := {z : E | 0 < z 0}
    Weak.MemW01p 2 F H ∧
    ∃ p : Fin n → E → ℝ,
      (∀ i, MemLp (p i) 2 (volume.restrict H)) ∧
      (∀ i, Weak.HasWeakPartialDeriv i (p i) F H) ∧
      (∀ i, MemLp (fun z => ∑ j, divergenceCoefficients g e z i j * p j z)
        2 (volume.restrict (W ∩ H))) ∧
      MemLp (fun z => g.pullbackVolumeDensity e z * f (e z))
        2 (volume.restrict (W ∩ H)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ H →
        (∫ z in W ∩ H, ∑ i, ∑ j, divergenceCoefficients g e z i j * p j z *
          fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z in W ∩ H, g.pullbackVolumeDensity e z * f (e z) * φ z) := by
  classical
  dsimp only
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hO : IsOpen (W ∩ H) := hW.inter hH
  have hOK : W ∩ H ⊆ closure W := inter_subset_left.trans subset_closure
  have hmeasure := Measure.restrict_mono (μ := volume)
    (show W ∩ H ⊆ H from inter_subset_right) le_rfl
  have hF : Weak.MemW01p 2 F H := memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat u
  choose p hp hw using hF.1.2
  have hFraw {z : E} (hz : z ∈ W ∩ H) : F z = toL2 D Ω u (e z) := by
    simp only [F, chartPullback_apply e _ (hWs (hOK hz)), hone z hz.1, one_mul]
  have hpeq (i : Fin n) : p i =ᵐ[volume.restrict (W ∩ H)]
      localCoordinateDerivative e he hei hWc hWs hOK (EuclideanSpace.single i 1) u := by
    have hraw : Weak.HasWeakPartialDeriv i (p i) (fun z => toL2 D Ω u (e z)) (W ∩ H) := by
      intro φ hφ hφc hφs
      calc
        _ = ∫ z in W ∩ H, F z * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
          apply setIntegral_congr_fun hO.measurableSet
          intro z hz
          dsimp only
          rw [hFraw hz]
        _ = _ := (hw i).restrict hO inter_subset_right φ hφ hφc hφs
    exact hraw.ae_eq hO (fun φ hφ hφc hφs =>
      localCoordinateDerivative_weak e he hei hWc hWs hOK hO u i hφ hφc hφs)
      (((hp i).mono_measure hmeasure).locallyIntegrable (by norm_num))
      ((Lp.memLp _).locallyIntegrable (by norm_num))
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) (closure W) := by
    intro z hz
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hWs hz)))
      (hD.mfderiv_injective (hWs hz))).1.continuousAt.continuousWithinAt
  refine ⟨hF, p, hp, hw, ?_, ?_, ?_⟩
  · intro i
    apply memLp_finsetSum
    intro j _
    exact memLp_compact_coeff_mul hWc hO.measurableSet hOK
      ((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono hWs)
      ((hp j).mono_measure hmeasure)
  · apply memLp_compact_coeff_mul hWc hO.measurableSet hOK hρ
    exact (Lp.memLp (g.localL2Pullback e he hei hWc hWs hOK f)).ae_eq
      (g.localL2Pullback_ae e he hei hWc hWs hOK f)
  · intro φ hφ hφc hφs
    have hΩ : e '' (W ∩ H) ⊆ Ω := by
      rintro y ⟨z, hz, rfl⟩
      exact (hflat z (hWs (hOK hz))).mpr hz.2
    have heq := weakSolution_divergence_local e he hei hWc hWs hOK hΩ u f hsol hφ hφc hφs
    rw [← heq]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hpeq] with z hz
    simp only [hz]



theorem exists_local_memWkp_two (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ (u : H1Zero D Ω) (lambda : ℝ),
        (∀ v : H1Zero D Ω,
          ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ) →
        Euclidean.MemWkp 2 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, W, B, hx, hxW, hW, hWc, hWs, he, hei, hflat, hχ, hc, hs, hone, hBA⟩ :=
    exists_chart_cutoff_elliptic g S x
  obtain ⟨V, hV, hxV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  have hVW' : V ⊆ W := subset_closure.trans hVW
  refine ⟨e, χ, V, hx, hxV (mem_singleton _), hV, hVc,
    hVW.trans (subset_closure.trans hWs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hVW' hz), hflat, ?_⟩
  intro u lambda heigen
  obtain ⟨hu, p, hp, hw, hF, hf, heq⟩ :=
    weakEigen_localized_divergence e he hei χ hχ hc hs hflat hW hWc hWs hone u lambda heigen
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  let f : E → ℝ := fun z => (lambda * g.pullbackVolumeDensity e z) * F z
  have hH : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hVH : IsOpen (V ∩ H) := hV.inter hH
  have hVHc : IsCompact (closure (V ∩ H)) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hsub : V ∩ H ⊆ W ∩ H := inter_subset_inter_left H hVW'
  have hmeasure := Measure.restrict_mono (μ := volume) hsub le_rfl
  have hmeasureH := Measure.restrict_mono (μ := volume)
    (show V ∩ H ⊆ H from inter_subset_right) le_rfl
  have hB := weakEquation_with_elliptic_extension B hW hBA hF heq
  have htan := BoundaryTangential.exists_tangential_weakPartial_of_local_weakEquation
    B hW hV hVc hVW hu hf hp hw hB.1 hB.2
  apply BoundaryNormal.memWkp_two_of_tangential_weakDerivatives B hVH hVHc
    (hu.1.1.mono_measure hmeasureH) (hf.mono_measure hmeasure)
    (fun i => (hp i).mono_measure hmeasureH)
    (fun i => (hw i).restrict hVH inter_subset_right) htan
  have hrestrict := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hsub
    (show EqOn B.a (divergenceCoefficients g e) (V ∩ H) from fun z hz => hBA (hVW' hz.1))
    (show ∀ i, EqOn (p i) (p i) (V ∩ H) from fun _ _ _ => rfl) heq
  intro φ hφ hφc hφs
  simpa only [Finset.sum_mul] using hrestrict φ hφ hφc hφs



theorem exists_local_eigenbasis_memWkp_two (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ i : EigenIndex D Ω,
        Euclidean.MemWkp 2 2 (chartPullback e (fun y => χ y * toL2 D Ω
          (energyEigenfunction D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
            S.isOpen S.isCompact_closure i) y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_memWkp_two D S x
  refine ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, ?_⟩
  intro i
  exact hreg _ (eigenvalue D Ω i)
    (energyEigenfunction_equation D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure i)



theorem exists_local_memWkp_two_of_weakSolution (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ (u : H1Zero D Ω) (f : Lp ℝ 2 g.volumeMeasure),
        (∀ v : H1Zero D Ω,
          ⟪u, v⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ = ⟪f, toL2 D Ω v⟫_ℝ) →
        Euclidean.MemWkp 2 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, W, B, hx, hxW, hW, hWc, hWs, he, hei, hflat, hχ, hc, hs, hone, hBA⟩ :=
    exists_chart_cutoff_elliptic g S x
  obtain ⟨V, hV, hxV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  have hVW' : V ⊆ W := subset_closure.trans hVW
  refine ⟨e, χ, V, hx, hxV (mem_singleton _), hV, hVc,
    hVW.trans (subset_closure.trans hWs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hVW' hz), hflat, ?_⟩
  intro u f hsol
  obtain ⟨hu, p, hp, hw, hF, hf, heq⟩ :=
    weakSolution_localized_divergence e he hei χ hχ hc hs hflat hW hWc hWs hone u f hsol
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hVH : IsOpen (V ∩ H) := hV.inter hH
  have hVHc : IsCompact (closure (V ∩ H)) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hsub : V ∩ H ⊆ W ∩ H := inter_subset_inter_left H hVW'
  have hmeasure := Measure.restrict_mono (μ := volume) hsub le_rfl
  have hmeasureH := Measure.restrict_mono (μ := volume)
    (show V ∩ H ⊆ H from inter_subset_right) le_rfl
  have hB := weakEquation_with_elliptic_extension B hW hBA hF heq
  have htan := BoundaryTangential.exists_tangential_weakPartial_of_local_weakEquation
    B hW hV hVc hVW hu hf hp hw hB.1 hB.2
  apply BoundaryNormal.memWkp_two_of_tangential_weakDerivatives B hVH hVHc
    (hu.1.1.mono_measure hmeasureH) (hf.mono_measure hmeasure)
    (fun i => (hp i).mono_measure hmeasureH)
    (fun i => (hw i).restrict hVH inter_subset_right) htan
  have hrestrict := Poincare.Analysis.Elliptic.weakEquation_congr_restrict hsub
    (show EqOn B.a (divergenceCoefficients g e) (V ∩ H) from fun z hz => hBA (hVW' hz.1))
    (show ∀ i, EqOn (p i) (p i) (V ∩ H) from fun _ _ _ => rfl) heq
  intro φ hφ hφc hφs
  simpa only [Finset.sum_mul] using hrestrict φ hφ hφc hφs

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
