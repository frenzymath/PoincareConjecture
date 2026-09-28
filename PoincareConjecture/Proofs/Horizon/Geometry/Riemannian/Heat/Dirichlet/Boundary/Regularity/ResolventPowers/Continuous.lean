import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ContinuousOperator








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

open Poincare.Analysis.Sobolev

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

local notation "E" => EuclideanSpace ℝ (Fin n)

private def resolventEnergyPower (D : LeviCivitaData g) (Ω : Set M) (j : ℕ) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] H1Zero D Ω :=
  (domainResolvent D Ω).comp ((domainL2Resolvent D Ω) ^ j)

private theorem toDomainL2_resolventEnergyPower (D : LeviCivitaData g) (j : ℕ)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    toDomainL2 D Ω (resolventEnergyPower D Ω j f) =
      ((domainL2Resolvent D Ω) ^ (j + 1)) f := by
  rw [pow_succ']
  rfl

private theorem resolventEnergyPower_apply_resolvent (D : LeviCivitaData g) (j : ℕ)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    resolventEnergyPower D Ω j (domainL2Resolvent D Ω f) =
      resolventEnergyPower D Ω (j + 1) f := by
  simp only [resolventEnergyPower, ContinuousLinearMap.comp_apply, pow_succ,
    mul_apply_eq_comp]

private theorem resolventEnergyPower_pairing (D : LeviCivitaData g)
    (hΩ : IsOpen Ω) (j : ℕ) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω))
    (w : H1Zero D Ω) :
    ⟪resolventEnergyPower D Ω (j + 1) f, w⟫_ℝ -
        ⟪toL2 D Ω (resolventEnergyPower D Ω (j + 1) f), toL2 D Ω w⟫_ℝ =
      ⟪toL2 D Ω (resolventEnergyPower D Ω j (f - domainL2Resolvent D Ω f)),
        toL2 D Ω w⟫_ℝ := by
  rw [map_sub, resolventEnergyPower_apply_resolvent, map_sub, inner_sub_left]
  congr 1
  rw [← inner_toDomainL2 hΩ.measurableSet, toDomainL2_resolventEnergyPower]
  exact domainResolvent_inner _ _

variable [NeZero n]

private theorem resolventPower_memWkp_on_precompact
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    {U : Set E} (hU : IsOpen U) (hUs : U ⊆ e.source)
    (hone : ∀ z ∈ U, χ (e z) = 1) (hΩ : IsOpen Ω)
    (B : NirenbergEuclidean.SmoothEllipticBilinearForm n univ)
    (hBA : EqOn B.a (divergenceCoefficients g e) U)
    (hBρ : EqOn B.c (g.pullbackVolumeDensity e) U) (r : ℕ) :
    ∀ {V : Set E}, IsOpen V → IsCompact (closure V) → closure V ⊆ U →
      ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        Euclidean.MemWkp r 2
          (chartPullback e (fun y => χ y * toL2 D Ω (resolventEnergyPower D Ω r f) y))
          (V ∩ {z : E | 0 < z 0}) := by
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  induction r with
  | zero =>
    intro V _ _ _ f
    apply Euclidean.MemWkp.zero_iff_memLp.mpr
    exact (memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat
      (resolventEnergyPower D Ω 0 f)).1.1.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)
  | succ r ih =>
    intro V hV hVc hVU f
    obtain ⟨W, hW, hVW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
    have hWU' : W ⊆ U := subset_closure.trans hWU
    let u := resolventEnergyPower D Ω (r + 1) f
    let v := resolventEnergyPower D Ω r (f - domainL2Resolvent D Ω f)
    obtain ⟨hu0, heq⟩ := weakSolution_chosen_divergence e he hei χ hχ hc hs hflat
      hW hWc (hWU.trans hUs) (fun z hz => hone z (hWU' hz)) B
      (hBA.mono hWU') (hBρ.mono hWU') u v
      (resolventEnergyPower_pairing D hΩ r f)
    have hWHc : IsCompact (closure (W ∩ H)) :=
      hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
    have hf := BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure r
      (hW.inter hH) hWHc (ih hW hWc hWU (f - domainL2Resolvent D Ω f)) B.smooth_c
    exact (BoundaryTangential.memWkp_add_two_of_local_weakEquation r B hW hV hVc hVW
      hu0 hf heq).le_succ

private theorem exists_local_resolventPower_memWkp (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ r : ℕ, ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        Euclidean.MemWkp r 2
          (chartPullback e (fun y => χ y * toL2 D Ω (resolventEnergyPower D Ω r f) y))
          (V ∩ {z : E | 0 < z 0}) := by
  obtain ⟨e, χ, W, hx, hxW, hW, hWc, hWs, he, hei, hχ, hc, hs, hone, hflat, _⟩ :=
    exists_local_memWkp_two_of_weakSolution D S x
  obtain ⟨U, hU, hxU, hUW, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  have hUW' : U ⊆ W := subset_closure.trans hUW
  have hUs : closure U ⊆ e.source := hUW.trans (subset_closure.trans hWs)
  obtain ⟨B, hBA, hBρ⟩ := exists_elliptic_form_on_compact (g := g) e he hei hUc hUs
  obtain ⟨V, hV, hxV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hU hxU
  refine ⟨e, χ, V, hx, hxV (mem_singleton _), hV, hVc,
    hVU.trans (subset_closure.trans hUs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hUW' (hVU (subset_closure hz))), hflat, ?_⟩
  intro r
  exact resolventPower_memWkp_on_precompact D e he hei χ hχ hc hs hflat hU
    (subset_closure.trans hUs) (fun z hz => hone z (hUW' hz)) S.isOpen B
    (hBA.mono subset_closure) (hBρ.mono subset_closure) r hV hVc hVU

private theorem exists_local_resolventPower_continuous (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (x : closure Ω) :
    ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
      ∃ F : M → ℝ, ContinuousOn F V ∧
        F =ᵐ[g.volumeMeasure.restrict (V ∩ Ω)]
          (toL2 D Ω (resolventEnergyPower D Ω (n + 1) f) : M → ℝ) ∧
        ∀ y ∈ V, y ∉ Ω → F y = 0 := by
  obtain ⟨e, χ, W, hx, hxW, hW, hWc, hWs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_resolventPower_memWkp D S x
  obtain ⟨V, hV, hxV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  obtain ⟨ψ, hψ, hψc, _, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hVc hW hVW
  let u := resolventEnergyPower D Ω (n + 1) f
  let U := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hVH : IsOpen (V ∩ H) := hV.inter hH
  have hVW' : V ⊆ W := subset_closure.trans hVW
  have hVs' : V ⊆ e.source := hVW'.trans (subset_closure.trans hWs)
  have hu0 : Weak.MemW01p 2 U H := memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat u
  have hw0 := BoundaryTangential.memW01p_mul_smooth hH hu0 hψ hψc
  have hwk := BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset (n + 1)
    hH hW (hreg (n + 1) f) hψ hψc hψs
  obtain ⟨F, hF, hUF, hzero⟩ := BoundaryEmbedding.exists_continuous_zero_extension
    hψc.mul_right hw0 hwk
  have hcoordinate : F =ᵐ[volume.restrict (V ∩ H)] fun z => toL2 D Ω u (e z) := by
    filter_upwards [ae_restrict_of_ae hUF, ae_restrict_mem hVH.measurableSet] with z hz hzV
    change H.indicator (ψ * U) z = F z at hz
    rw [indicator_of_mem hzV.2, Pi.mul_apply, hψone z (subset_closure hzV.1), one_mul] at hz
    dsimp only [U] at hz
    rw [chartPullback_apply e _ (hVs' hzV.1), hone z (hVW' hzV.1), one_mul] at hz
    exact hz.symm
  have hVt : e '' V ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hVs' hz)
  have himage : e '' V ∩ Ω = e '' (V ∩ H) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzΩ⟩
      exact ⟨z, ⟨hz, (hflat z (hVs' hz)).mp hzΩ⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzH⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hflat z (hVs' hz)).mpr hzH⟩
  refine ⟨e '' V, e.isOpen_image_of_subset_source hV hVs',
    ⟨e.symm x, hxV (mem_singleton _), e.right_inv hx⟩, fun y => F (e.symm y),
    hF.comp_continuousOn (e.symm.continuousOn.mono hVt), ?_, ?_⟩
  · rw [himage]
    exact g.coordinate_representative_ae e he hei hVH
      (inter_subset_left.trans hVs') hcoordinate
  · rintro y ⟨z, hz, rfl⟩ hyΩ
    dsimp only
    rw [e.left_inv (hVs' hz)]
    exact hzero z (not_lt.mp (fun h => hyΩ ((hflat z (hVs' hz)).mpr h)))

omit [NeZero n] in
private theorem exists_continuous_zero_extension_of_local
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) (v : M → ℝ)
    (hlocal : ∀ x : closure Ω, ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
      ∃ F : M → ℝ, ContinuousOn F V ∧
        F =ᵐ[g.volumeMeasure.restrict (V ∩ Ω)] v ∧
        ∀ y ∈ V, y ∉ Ω → F y = 0) :
    ∃ F : M → ℝ, Continuous F ∧ HasCompactSupport F ∧
      F =ᵐ[g.volumeMeasure.restrict Ω] v ∧ ∀ x ∉ Ω, F x = 0 := by
  classical
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  choose V hVo hxV G hGc hGae hGzero using hlocal
  have hcompat (i j : closure Ω) : EqOn (G i) (G j) (V i ∩ V j) := by
    have hΩeq : EqOn (G i) (G j) ((V i ∩ V j) ∩ Ω) := by
      have hi : (V i ∩ V j) ∩ Ω ⊆ V i ∩ Ω := fun _ h => ⟨h.1.1, h.2⟩
      have hj : (V i ∩ V j) ∩ Ω ⊆ V j ∩ Ω := fun _ h => ⟨h.1.2, h.2⟩
      apply Measure.eqOn_open_of_ae_eq (μ := g.volumeMeasure)
        (Filter.EventuallyEq.trans
          (ae_restrict_of_ae_restrict_of_subset hi (hGae i))
          (Filter.EventuallyEq.symm
            (ae_restrict_of_ae_restrict_of_subset hj (hGae j))))
        (((hVo i).inter (hVo j)).inter hΩ)
        ((hGc i).mono (fun _ h => h.1.1)) ((hGc j).mono (fun _ h => h.1.2))
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact hΩeq ⟨hx, hxΩ⟩
    · rw [hGzero i x hx.1 hxΩ, hGzero j x hx.2 hxΩ]
  let F : M → ℝ := fun x => if hx : x ∈ closure Ω then G ⟨x, hx⟩ x else 0
  have hzero (x : M) (hx : x ∉ Ω) : F x = 0 := by
    dsimp only [F]
    split_ifs with hxc
    · exact hGzero ⟨x, hxc⟩ x (hxV ⟨x, hxc⟩) hx
    · rfl
  have hFG (i : closure Ω) : EqOn F (G i) (V i) := by
    intro x hx
    by_cases hxc : x ∈ closure Ω
    · simpa only [F, dif_pos hxc] using hcompat ⟨x, hxc⟩ i ⟨hxV ⟨x, hxc⟩, hx⟩
    · simp only [F, dif_neg hxc]
      exact (hGzero i x hx (fun h => hxc (subset_closure h))).symm
  have hFc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ closure Ω
    · let i : closure Ω := ⟨x, hx⟩
      have heq : F =ᶠ[𝓝 x] G i :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨V i, (hVo i).mem_nhds (hxV i), hFG i⟩
      exact ((hGc i).continuousAt ((hVo i).mem_nhds (hxV i))).congr_of_eventuallyEq heq
    · have heq : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
        exact hzero y (fun h => hy (subset_closure h))
      exact continuousAt_const.congr_of_eventuallyEq heq
  have hs : tsupport F ⊆ closure Ω := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  obtain ⟨s, hcover⟩ := hc.elim_finite_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  have hFae (i : closure Ω) : F =ᵐ[g.volumeMeasure.restrict (V i ∩ Ω)] v :=
    (Filter.EventuallyEq.trans
      ((ae_restrict_iff' ((hVo i).inter hΩ).measurableSet).mpr
        (ae_of_all _ fun x hx => hFG i hx.1)) (hGae i))
  have hall : ∀ᵐ x ∂g.volumeMeasure, ∀ i : s, x ∈ V i.1 ∩ Ω → F x = v x :=
    ae_all_iff.mpr fun i => ae_imp_of_ae_restrict (hFae i.1)
  refine ⟨F, hFc, hc.of_isClosed_subset isClosed_closure hs,
    (ae_restrict_iff' hΩ.measurableSet).mpr ?_, hzero⟩
  filter_upwards [hall] with x hx hxΩ
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover (subset_closure hxΩ))
  exact hx ⟨i, hi⟩ ⟨hxi, hxΩ⟩

private theorem exists_resolventPower_representative (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ∃ F : M →ᵇ ℝ, (F : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      (((domainL2Resolvent D Ω) ^ (n + 2)) f : M → ℝ) ∧
      ∀ x ∉ Ω, F x = 0 := by
  obtain ⟨F, hFc, hFcomp, hFae, hFzero⟩ := exists_continuous_zero_extension_of_local
    S.isOpen S.isCompact_closure
    (toL2 D Ω (resolventEnergyPower D Ω (n + 1) f))
    (exists_local_resolventPower_continuous D S f)
  obtain ⟨C, hC⟩ := hFcomp.exists_bound_of_continuous hFc
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup F hFc C hC, ?_, hFzero⟩
  have h := toDomainL2_ae (resolventEnergyPower D Ω (n + 1) f)
  rw [toDomainL2_resolventEnergyPower] at h
  exact hFae.trans h.symm



theorem exists_resolventPower_continuousLinearMap (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) :
    ∃ T : Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ),
      ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        (T f : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
          (((domainL2Resolvent D Ω) ^ (n + 2)) f : M → ℝ) ∧
        ∀ x : M, x ∉ Ω → T f x = 0 := by
  classical
  let : IsFiniteMeasure (g.volumeMeasure.restrict Ω) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt
      (g.volumeMeasure_lt_top_of_isCompact S.isCompact_closure)).ne
  let P := (domainL2Resolvent D Ω) ^ (n + 2)
  choose F hFae hFzero using exists_resolventPower_representative D S
  let J : (M →ᵇ ℝ) →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
    BoundedContinuousFunction.toLp 2 (g.volumeMeasure.restrict Ω) ℝ
  have hJ (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) : J (F f) = P f := by
    apply Lp.ext
    exact (BoundedContinuousFunction.coeFn_toLp 2 _ ℝ (F f)).trans (hFae f)
  have huniq {A B : M →ᵇ ℝ} (h : J A = J B)
      (hA : ∀ x ∉ Ω, A x = 0) (hB : ∀ x ∉ Ω, B x = 0) : A = B := by
    apply boundedContinuous_eq_of_ae (g := g) S.isOpen _ hA hB
    exact (BoundedContinuousFunction.coeFn_toLp 2 _ ℝ A).symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun v : Lp ℝ 2
        (g.volumeMeasure.restrict Ω) => (v : M → ℝ)) h)).trans
        (BoundedContinuousFunction.coeFn_toLp 2 _ ℝ B))
  let T : Lp ℝ 2 (g.volumeMeasure.restrict Ω) →ₗ[ℝ] (M →ᵇ ℝ) :=
    { toFun := F
      map_add' := by
        intro f h
        apply huniq
        · change J (F (f + h)) = J (F f + F h)
          simp only [map_add, hJ]
        · exact hFzero (f + h)
        · intro x hx
          simp [hFzero f x hx, hFzero h x hx]
      map_smul' := by
        intro c f
        apply huniq
        · change J (F (c • f)) = J (c • F f)
          simp only [map_smul, hJ]
        · exact hFzero (c • f)
        · intro x hx
          simp [hFzero f x hx] }
  have hTc : Continuous T := by
    apply T.continuous_of_seq_closed_graph
    intro u f G hu hG
    have hJlim : Tendsto (fun i => J (T (u i))) atTop (𝓝 (J G)) :=
      (J.continuous.tendsto G).comp hG
    have hPlim : Tendsto (fun i => J (T (u i))) atTop (𝓝 (P f)) := by
      have heq : (fun i => J (T (u i))) = P ∘ u := funext fun i => hJ (u i)
      rw [heq]
      exact (P.continuous.tendsto f).comp hu
    apply huniq
    · change J G = J (T f)
      rw [show J (T f) = P f from hJ f]
      exact tendsto_nhds_unique hJlim hPlim
    · intro x hx
      have heval : Tendsto (fun i => T (u i) x) atTop (𝓝 (G x)) :=
        ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto G).comp hG
      have hzseq : (fun i => T (u i) x) = fun _ => (0 : ℝ) :=
        funext fun i => hFzero (u i) x hx
      rw [hzseq] at heval
      exact tendsto_nhds_unique heval tendsto_const_nhds
    · exact hFzero f
  exact ⟨⟨T, hTc⟩, fun f => ⟨hFae f, hFzero f⟩⟩

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
