import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.H2
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.WeakEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.H3

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

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_elliptic_form_on_compact
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ,
      EqOn B.a (divergenceCoefficients g e) K ∧ EqOn B.c (g.pullbackVolumeDensity e) K := by
  have hpos {z : E} (hz : z ∈ e.source) : Matrix.PosDef (divergenceCoefficients g e z) := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, fun v hv => ?_⟩
    · apply Matrix.IsHermitian.ext
      intro i j
      simpa only [star_trivial] using divergenceCoefficients_symm (g := g) e he hei hz j i
    · let w : E := WithLp.toLp 2 v
      have hw : w ≠ 0 := by
        intro h
        exact hv (congrArg WithLp.ofLp h)
      have hp := divergenceCoefficients_pos (g := g) e he hei hz w hw
      simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
        w, WithLp.ofLp_toLp, mul_left_comm, mul_assoc] using hp
  have hρ : ContDiffOn ℝ ∞ (g.pullbackVolumeDensity e) e.source := by
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    intro z hz
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hz))
      (hD.mfderiv_injective hz)).1.contDiffWithinAt
  obtain ⟨W, _, hKW, _, _, B, hBA, hBρ⟩ :=
    Poincare.Analysis.Elliptic.exists_global_elliptic_extension e.open_source hK hKs
      (divergenceCoefficients g e) (g.pullbackVolumeDensity e)
      (contDiffOn_divergenceCoefficients e he hei) (fun z hz => hpos hz) hρ
  exact ⟨B, hBA.mono hKW, hBρ.mono hKW⟩

private theorem localized_eigenfunction_data
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {U : Set E} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUs : closure U ⊆ e.source) (hone : ∀ z ∈ U, χ (e z) = 1)
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ)
    (hBA : EqOn B.a (divergenceCoefficients g e) U)
    (hBρ : EqOn B.c (g.pullbackVolumeDensity e) U)
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U)
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    (hu2 : Euclidean.MemWkp 2 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
      (U ∩ {z : E | 0 < z 0})) :
    let w := fun z => ψ z * chartPullback e (fun y => χ y * toL2 D Ω u y) z
    let H := {z : E | 0 < z 0}
    Weak.MemW01p 2 w H ∧ Euclidean.MemWkp 2 2 w H ∧
      ∃ f : E → ℝ, Weak.MemW1p 2 f H ∧
        ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ H →
          (∫ z in H, ∑ i, ∑ j, B.a z i j * Euclidean.chosenWeakPartial' 2 j w H z *
            fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z in H, f z * φ z := by
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hUH : IsOpen (U ∩ H) := hU.inter hH
  have hUHc : IsCompact (closure (U ∩ H)) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨hu0, p, hp, hw, _, _, heq⟩ :=
    weakEigen_localized_divergence e he hei χ hχ hc hs hflat hU hUc hUs hone u lambda heigen
  have hchosen (j : Fin n) : Euclidean.chosenWeakPartial' 2 j F (U ∩ H) =ᵐ[volume.restrict (U ∩ H)]
      p j := by
    exact Weak.HasWeakPartialDeriv.ae_eq hUH
      (Euclidean.chosenWeakPartial'_isWeakPartial_of_mem hu2.memW1p j)
      ((hw j).restrict hUH inter_subset_right)
      ((Euclidean.chosenWeakPartial'_memLp_of_mem hu2.memW1p j).locallyIntegrable (by norm_num))
      (((hp j).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).locallyIntegrable
        (by norm_num))
  let f : E → ℝ := fun z => (lambda * B.c z) * F z
  have hf : Euclidean.MemWkp 1 2 f (U ∩ H) :=
    BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure 1 hUH hUHc hu2.le_succ
      (contDiff_const.mul B.smooth_c)
  have hB : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U ∩ H →
      (∫ z in U ∩ H, ∑ i, ∑ j, B.a z i j * Euclidean.chosenWeakPartial' 2 j F (U ∩ H) z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z in U ∩ H, f z * φ z := by
    intro φ hφ hφc hφs
    calc
      _ = ∫ z in U ∩ H, ∑ i, ∑ j, divergenceCoefficients g e z i j * p j z *
          fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUH.measurableSet, eventually_all.mpr hchosen] with z hz hpz
        simp only [hBA hz.1, hpz]
      _ = _ := heq φ hφ hφc hφs
      _ = ∫ z in U ∩ H, f z * φ z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUH.measurableSet] with z hz
        simp only [f, hBρ hz.1, F]
  have hloc := BoundaryLocalization.localize_weak_divergence 1 hH hU B.a B.smooth_a
    hu2 hf hψ hψc hψs hB
  exact ⟨BoundaryTangential.memW01p_mul_smooth hH hu0 hψ hψc,
    BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset 2 hH hU hu2 hψ hψc hψs,
    _, hloc.1.memW1p, hloc.2⟩

theorem exists_local_memWkp_three (D : LeviCivitaData g)
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
        Euclidean.MemWkp 3 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_memWkp_two D S x
  obtain ⟨U, hU, hxU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hV (singleton_subset_iff.mpr hxV)
  have hUV' : U ⊆ V := subset_closure.trans hUV
  have hUs : closure U ⊆ e.source := hUV.trans (subset_closure.trans hVs)
  obtain ⟨B, hBA, hBρ⟩ := exists_elliptic_form_on_compact (g := g) e he hei hUc hUs
  obtain ⟨T, hT, hxT, hTU, hTc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hU hxU
  obtain ⟨ψ, hψ, hψc, _, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hTc hU hTU
  refine ⟨e, χ, T, hx, hxT (mem_singleton _), hT, hTc,
    hTU.trans (subset_closure.trans hUs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hUV' (hTU (subset_closure hz))), hflat, ?_⟩
  intro u lambda heigen
  have hH : IsOpen {z : E | 0 < z 0} := BoundaryTangential.isOpen_halfSpace
  have hu2 := (hreg u lambda heigen).mono_set (by norm_num) (hU.inter hH)
    (inter_subset_inter_left _ hUV')
  obtain ⟨hu0, hu2global, f, hf, heq⟩ :=
    localized_eigenfunction_data e he hei χ hχ hc hs hflat hU hUc hUs
      (fun z hz => hone z (hUV' hz)) B (hBA.mono subset_closure) (hBρ.mono subset_closure)
      hψ hψc hψs u lambda heigen hu2
  have hu3 := BoundaryTangential.memWkp_three_of_weakEquation B hT hTc hu0 hu2global hf heq
  apply (Euclidean.MemWkp_congr_ae (by norm_num) (hT.inter hH) _).mp hu3
  filter_upwards [ae_restrict_mem (hT.inter hH).measurableSet] with z hz
  simp only [hψone z (subset_closure hz.1), one_mul]

theorem exists_local_eigenbasis_memWkp_three (D : LeviCivitaData g)
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
        Euclidean.MemWkp 3 2 (chartPullback e (fun y => χ y * toL2 D Ω
          (energyEigenfunction D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
            S.isOpen S.isCompact_closure i) y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_memWkp_three D S x
  refine ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, ?_⟩
  intro i
  exact hreg _ (eigenvalue D Ω i)
    (energyEigenfunction_equation D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure i)

private theorem localized_energy_forcing_data
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {U : Set E} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUs : closure U ⊆ e.source) (hone : ∀ z ∈ U, χ (e z) = 1)
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ)
    (hBA : EqOn B.a (divergenceCoefficients g e) U)
    (hBρ : EqOn B.c (g.pullbackVolumeDensity e) U)
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U)
    (u v : H1Zero D Ω)
    (hsol : ∀ w : H1Zero D Ω,
      ⟪u, w⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω w⟫_ℝ = ⟪toL2 D Ω v, toL2 D Ω w⟫_ℝ)
    (hu2 : Euclidean.MemWkp 2 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
      (U ∩ {z : E | 0 < z 0})) :
    let w := fun z => ψ z * chartPullback e (fun y => χ y * toL2 D Ω u y) z
    let H := {z : E | 0 < z 0}
    Weak.MemW01p 2 w H ∧ Euclidean.MemWkp 2 2 w H ∧
      ∃ f : E → ℝ, Weak.MemW1p 2 f H ∧
        ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ H →
          (∫ z in H, ∑ i, ∑ j, B.a z i j * Euclidean.chosenWeakPartial' 2 j w H z *
            fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z in H, f z * φ z := by
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let G := chartPullback e (fun y => χ y * toL2 D Ω v y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hUH : IsOpen (U ∩ H) := hU.inter hH
  have hUHc : IsCompact (closure (U ∩ H)) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨hu0, p, hp, hw, _, _, heq⟩ := weakSolution_localized_divergence
    e he hei χ hχ hc hs hflat hU hUc hUs hone u (toL2 D Ω v) hsol
  have hchosen (j : Fin n) : Euclidean.chosenWeakPartial' 2 j F (U ∩ H) =ᵐ[volume.restrict (U ∩ H)]
      p j := by
    exact Weak.HasWeakPartialDeriv.ae_eq hUH
      (Euclidean.chosenWeakPartial'_isWeakPartial_of_mem hu2.memW1p j)
      ((hw j).restrict hUH inter_subset_right)
      ((Euclidean.chosenWeakPartial'_memLp_of_mem hu2.memW1p j).locallyIntegrable (by norm_num))
      (((hp j).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).locallyIntegrable
        (by norm_num))
  have hG : Euclidean.MemWkp 1 2 G (U ∩ H) :=
    Euclidean.MemWkp.one_iff_memW1p.mpr (Euclidean.MemW1p.mono_set hUH inter_subset_right
      (memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat v).1)
  let f : E → ℝ := fun z => B.c z * G z
  have hf : Euclidean.MemWkp 1 2 f (U ∩ H) :=
    BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure 1 hUH hUHc hG B.smooth_c
  have hB : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U ∩ H →
      (∫ z in U ∩ H, ∑ i, ∑ j, B.a z i j * Euclidean.chosenWeakPartial' 2 j F (U ∩ H) z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z in U ∩ H, f z * φ z := by
    intro φ hφ hφc hφs
    calc
      _ = ∫ z in U ∩ H, ∑ i, ∑ j, divergenceCoefficients g e z i j * p j z *
          fderiv ℝ φ z (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUH.measurableSet, eventually_all.mpr hchosen] with z hz hpz
        simp only [hBA hz.1, hpz]
      _ = _ := heq φ hφ hφc hφs
      _ = ∫ z in U ∩ H, f z * φ z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hUH.measurableSet] with z hz
        simp only [f, hBρ hz.1, G, chartPullback_apply e _ (hUs (subset_closure hz.1)),
          hone z hz.1, one_mul]
  have hloc := BoundaryLocalization.localize_weak_divergence 1 hH hU B.a B.smooth_a
    hu2 hf hψ hψc hψs hB
  exact ⟨BoundaryTangential.memW01p_mul_smooth hH hu0 hψ hψc,
    BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset 2 hH hU hu2 hψ hψc hψs,
    _, hloc.1.memW1p, hloc.2⟩

theorem exists_local_memWkp_three_of_energy_forcing (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ u w : H1Zero D Ω,
        (∀ v : H1Zero D Ω,
          ⟪u, v⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ = ⟪toL2 D Ω w, toL2 D Ω v⟫_ℝ) →
        Euclidean.MemWkp 3 2 (chartPullback e (fun y => χ y * toL2 D Ω u y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_memWkp_two_of_weakSolution D S x
  obtain ⟨U, hU, hxU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hV (singleton_subset_iff.mpr hxV)
  have hUV' : U ⊆ V := subset_closure.trans hUV
  have hUs : closure U ⊆ e.source := hUV.trans (subset_closure.trans hVs)
  obtain ⟨B, hBA, hBρ⟩ := exists_elliptic_form_on_compact (g := g) e he hei hUc hUs
  obtain ⟨T, hT, hxT, hTU, hTc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hU hxU
  obtain ⟨ψ, hψ, hψc, _, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hTc hU hTU
  refine ⟨e, χ, T, hx, hxT (mem_singleton _), hT, hTc,
    hTU.trans (subset_closure.trans hUs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hUV' (hTU (subset_closure hz))), hflat, ?_⟩
  intro u w hsol
  have hH : IsOpen {z : E | 0 < z 0} := BoundaryTangential.isOpen_halfSpace
  have hu2 := (hreg u (toL2 D Ω w) hsol).mono_set (by norm_num) (hU.inter hH)
    (inter_subset_inter_left _ hUV')
  obtain ⟨hu0, hu2global, f, hf, heq⟩ :=
    localized_energy_forcing_data e he hei χ hχ hc hs hflat hU hUc hUs
      (fun z hz => hone z (hUV' hz)) B (hBA.mono subset_closure) (hBρ.mono subset_closure)
      hψ hψc hψs u w hsol hu2
  have hu3 := BoundaryTangential.memWkp_three_of_weakEquation B hT hTc hu0 hu2global hf heq
  apply (Euclidean.MemWkp_congr_ae (by norm_num) (hT.inter hH) _).mp hu3
  filter_upwards [ae_restrict_mem (hT.inter hH).measurableSet] with z hz
  simp only [hψone z (subset_closure hz.1), one_mul]

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
