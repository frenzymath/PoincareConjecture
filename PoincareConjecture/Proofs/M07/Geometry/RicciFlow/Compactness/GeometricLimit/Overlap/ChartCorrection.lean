import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

private theorem exists_compact_overlap_cutoff {n : ℕ}
    {K V : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ EqOn χ 1 K := by
  obtain ⟨C, hC, hCc, hKC, hCV⟩ := exists_compact_closed_between hK hV hKV
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓡 n) hK.isClosed hKC (n := ⊤)
  have hsupport : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ C := by
    apply closure_minimal _ hCc
    intro x hx
    by_contra hxc
    exact hx (hχzero x hxc)
  refine ⟨χ, χ.contMDiff.contDiff, hC.of_isClosed_subset isClosed_closure hsupport,
    hsupport.trans hCV, ?_⟩
  intro x hx
  exact hχone.self_of_nhdsSet x hx

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in
theorem eventually_exists_source_chart_correction
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hχV : tsupport χ ⊆ Subtype.val '' overlap (fun i j => D i j) j i) :
    ∀ᶠ k in atTop, ∃ a : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ a.symm ∧
      (∀ y, y ∉ tsupport χ → a y = y) ∧ a '' U j = U j ∧
      (∀ y, a y = y + χ y •
        (coordinateRepresentative U hU (fun x => Function.invFun (e k j) (e k i x))
          (coordinateRepresentative U hU (transition (fun i j => D i j) j i) y) - y)) ∧
      ∀ x : Piece U i, x ∈ overlap (fun i j => D i j) i j →
        χ (transition (fun i j => D i j) i j x) = 1 →
        chartParametrization U hU (e k j)
          (a (transition (fun i j => D i j) i j x)) = e k i x := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let A := Subtype.val '' overlap (fun i j => D i j) i j
  let B := Subtype.val '' overlap (fun i j => D i j) j i
  let f := coordinateRepresentative U hU (transition (fun i j => D i j) i j)
  let g := coordinateRepresentative U hU (transition (fun i j => D i j) j i)
  let fs := fun k => coordinateRepresentative U hU
    (fun x => Function.invFun (e k j) (e k i x))
  have hopen' (a b : ι) : IsOpen (Subtype.val '' overlap (fun i j => D i j) a b) :=
    (hU a).isOpenEmbedding_subtypeVal.isOpenMap _
      (isOpen_overlap hD L he c hc hlower hopen hconn a b)
  have hs (a b : ι) : ContDiffOn ℝ ∞
      (coordinateRepresentative U hU (transition (fun i j => D i j) a b))
      (Subtype.val '' overlap (fun i j => D i j) a b) :=
    contDiffOn_of_locally_eventually_smooth
      (fun _ hx => coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn a b hx)
      (fun _ hx => exists_eventually_contDiffOn_coordinate_source_transition U hU hD L he c hc
        hlower hopen hconn hsmooth a b hx) (hbound a b)
  have hgA : MapsTo g B A := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨transition (fun i j => D i j) j i y, transition_mem hD hy,
      (coordinateRepresentative_apply U hU _ y).symm⟩
  have hfg : EqOn (f ∘ g) id B := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, f, g, coordinateRepresentative_apply, id_eq,
      transition_inverse hD c hc hlower hy]
  have hz (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKA : K ⊆ A) :
      TendstoUniformlyOn fs f atTop K := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
      (tendstoUniformlyOn_coordinate_source_transition_jet U hU hD L he c hc hlower
        hopen hconn hsmooth i j (hbound i j) 0 hK hKA)
  have ho (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKA : K ⊆ A) :
      TendstoUniformlyOn (fun k => fderiv ℝ (fs k)) (fderiv ℝ f) atTop K := by
    have hid (q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
        (fun x => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin n)) (iteratedFDeriv ℝ 1 q x)) =
          fderiv ℝ q := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simpa only [Function.comp_def, hid] using
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n))).isometry.uniformContinuous.comp_tendstoUniformlyOn
      (tendstoUniformlyOn_coordinate_source_transition_jet U hU hD L he c hc hlower
        hopen hconn hsmooth i j (hbound i j) 1 hK hKA)
  have hcor := eventually_exists_local_transition_correction (hopen' i j) (hopen' j i)
    (hs i j) (hs j i) hgA hfg (fun x hx => by
      obtain ⟨V, hV, hxV, _, hv⟩ := exists_eventually_contDiffOn_coordinate_source_transition
        U hU hD L he c hc hlower hopen hconn hsmooth i j hx
      exact ⟨V, hV, hxV, hv⟩) hz ho hχ hχcompact hχV
  have hKA : g '' tsupport χ ⊆ A := image_subset_iff.mpr (fun _ hx => hgA (hχV hx))
  let C : Set (Piece U i) := Subtype.val ⁻¹' (g '' tsupport χ)
  have hCimage : Subtype.val '' C = g '' tsupport χ := by
    apply image_preimage_eq_of_subset
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, _, hy⟩ := hKA (mem_image_of_mem g hx)
    exact ⟨y, hy⟩
  have hC : IsCompact C := (hU i).isOpenEmbedding_subtypeVal.isEmbedding.isCompact_iff.mpr
    (hCimage ▸ hχcompact.isCompact.image_of_continuousOn ((hs j i).continuousOn.mono hχV))
  have hCoverlap : C ⊆ overlap (fun i j => D i j) i j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hKA hx
    have : y = x := Subtype.ext hxy
    exact this ▸ hy
  obtain ⟨K, _, hrep⟩ := exists_compact_source_transition_target hD L he c hc hlower
    hopen hconn hC hCoverlap
  filter_upwards [hcor, hrep] with k hk hkr
  obtain ⟨a, haformula, ha, hai, haone, hafix, _⟩ := hk
  refine ⟨a, ha, hai, hafix, ?_, haformula, ?_⟩
  · have hsupport : tsupport χ ⊆ U j := hχV.trans (by rintro _ ⟨y, _, rfl⟩; exact y.property)
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_contra hy
      have hxy := a.injective (hafix (a x) (fun h => hy (hsupport h)))
      exact hy (hxy.symm ▸ hx)
    · intro hy
      refine ⟨a.symm y, ?_, a.apply_symm_apply y⟩
      by_contra hx
      have hey := hafix (a.symm y) (fun h => hx (hsupport h))
      rw [a.apply_symm_apply] at hey
      exact hx (hey ▸ hy)
  · intro x hx hχx
    have hxs : (transition (fun i j => D i j) i j x : EuclideanSpace ℝ (Fin n)) ∈ tsupport χ :=
      subset_tsupport χ (by simp [Function.mem_support, hχx])
    have hginv : g (transition (fun i j => D i j) i j x) = (x : EuclideanSpace ℝ (Fin n)) := by
      simp only [g, coordinateRepresentative_apply, transition_inverse hD c hc hlower hx]
    have hxC : x ∈ C := ⟨_, hxs, hginv⟩
    rw [haone _ hχx]
    change chartParametrization U hU (e k j)
      (fs k (g (transition (fun i j => D i j) i j x))) = e k i x
    rw [hginv]
    simp only [fs, coordinateRepresentative_apply, chartParametrization_apply]
    exact Function.invFun_eq (image_subset_range _ _ (hkr x hxC).1)

include hD he hc hlower hopen hconn hsmooth in

theorem exists_eventual_source_chart_correction_on_compact
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {K : Set (Piece U j)} (hK : IsCompact K)
    (hKoverlap : K ⊆ overlap (fun i j => D i j) j i) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      S ⊆ Subtype.val '' overlap (fun i j => D i j) j i ∧
      ∀ᶠ k in atTop, ∃ a : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
        ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ a.symm ∧
        (∀ y, y ∉ S → a y = y) ∧ a '' U j = U j ∧
        ∀ x : Piece U i, x ∈ overlap (fun i j => D i j) i j →
          transition (fun i j => D i j) i j x ∈ K →
          chartParametrization U hU (e k j)
            (a (transition (fun i j => D i j) i j x)) = e k i x := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := exists_compact_overlap_cutoff
    (hK.image continuous_subtype_val)
    ((hU j).isOpenEmbedding_subtypeVal.isOpenMap _
      (isOpen_overlap hD L he c hc hlower hopen hconn j i)) (image_mono hKoverlap)
  refine ⟨tsupport χ, hχc.isCompact, hχs, ?_⟩
  filter_upwards [eventually_exists_source_chart_correction U hU hD L he c hc hlower
    hopen hconn hsmooth hbound i j hχ hχc hχs] with k hk
  obtain ⟨a, ha, hai, hafix, haU, _, haeq⟩ := hk
  exact ⟨a, ha, hai, hafix, haU, fun x hx hxK =>
    haeq x hx (hχone (mem_image_of_mem Subtype.val hxK))⟩

include hD he hc hlower hopen hconn hsmooth in
theorem tendstoUniformlyOn_source_chart_correction_jet
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hχV : tsupport χ ⊆ Subtype.val '' overlap (fun i j => D i j) j i)
    {a : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (ha : ∀ᶠ k in atTop, ∀ y, a k y = y + χ y •
      (coordinateRepresentative U hU (fun x => Function.invFun (e k j) (e k i x))
        (coordinateRepresentative U hU (transition (fun i j => D i j) j i) y) - y))
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
      (iteratedFDeriv ℝ m id) atTop K := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let A := Subtype.val '' overlap (fun i j => D i j) i j
  let B := Subtype.val '' overlap (fun i j => D i j) j i
  let g := coordinateRepresentative U hU (transition (fun i j => D i j) j i)
  let fs := fun k => coordinateRepresentative U hU
    (fun x => Function.invFun (e k j) (e k i x))
  have hBo : IsOpen B := (hU j).isOpenEmbedding_subtypeVal.isOpenMap _
    (isOpen_overlap hD L he c hc hlower hopen hconn j i)
  have hg : ContDiffOn ℝ ∞ g B :=
    contDiffOn_of_locally_eventually_smooth
      (fun _ hx => coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn j i hx)
      (fun _ hx => exists_eventually_contDiffOn_coordinate_source_transition U hU hD L he c hc
        hlower hopen hconn hsmooth j i hx) (hbound j i)
  have hgA : MapsTo g B A := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨transition (fun i j => D i j) j i y, transition_mem hD hy,
      (coordinateRepresentative_apply U hU _ y).symm⟩
  have hlocal : ∀ x ∈ A, ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fs k) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hWs⟩ := exists_eventually_contDiffOn_coordinate_source_transition
      U hU hD L he c hc hlower hopen hconn hsmooth i j hx
    exact ⟨W, hW, hxW, hWs⟩
  have hpoint : ∀ y ∈ B, Tendsto (fun k => (fs k ∘ g) y) atTop (𝓝 y) := by
    rintro _ ⟨y, hy, rfl⟩
    have ht := coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn
      i j (mem_image_of_mem Subtype.val (transition_mem hD hy))
    simpa only [fs, g, Function.comp_apply, coordinateRepresentative_apply,
      transition_inverse hD c hc hlower hy] using ht
  have hjet := tendstoUniformlyOn_cutoff_perturbation_jet hpoint
    (locally_eventually_smooth_comp_fixed hBo hg hgA hlocal)
    ((hbound i j).comp_fixed hBo hg hgA hlocal) hχ hχcompact hχV m hK
  apply hjet.congr
  filter_upwards [ha] with k hk x _
  exact congrArg (fun q => iteratedFDeriv ℝ m q x) (funext hk).symm

include hD hc hlower hopen in
omit [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] in

theorem source_chart_correction_fixes_agreement
    (i j : ι) (k : ℕ) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (ha : ∀ y, a y = y + χ y •
      (coordinateRepresentative U hU (fun x => Function.invFun (e k j) (e k i x))
        (coordinateRepresentative U hU (transition (fun i j => D i j) j i) y) - y))
    {x : Piece U i} (hx : x ∈ overlap (fun i j => D i j) i j)
    (hagree : e k i x = e k j (transition (fun i j => D i j) i j x)) :
    a (transition (fun i j => D i j) i j x) = transition (fun i j => D i j) i j x := by
  rw [ha]
  simp only [coordinateRepresentative_apply, transition_inverse hD c hc hlower hx]
  rw [hagree, Function.leftInverse_invFun (hopen k j).injective]
  simp only [sub_self, smul_zero, add_zero]

include hD he hc hlower hopen hconn hsmooth in

theorem exists_smooth_relative_source_chart_corrections_on_compact
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {K : Set (Piece U j)} (hK : IsCompact K)
    (hKoverlap : K ⊆ overlap (fun i j => D i j) j i) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      S ⊆ Subtype.val '' overlap (fun i j => D i j) j i ∧
      ∃ a : ℕ → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
        (∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
          (∀ y, y ∉ S → a k y = y) ∧ (a k) '' U j = U j ∧
          (∀ x : Piece U i, x ∈ overlap (fun i j => D i j) i j →
            transition (fun i j => D i j) i j x ∈ K →
            chartParametrization U hU (e k j)
              (a k (transition (fun i j => D i j) i j x)) = e k i x) ∧
          ∀ x : Piece U i, x ∈ overlap (fun i j => D i j) i j →
            e k i x = e k j (transition (fun i j => D i j) i j x) →
            a k (transition (fun i j => D i j) i j x) =
              transition (fun i j => D i j) i j x) ∧
        ∀ m (C : Set (EuclideanSpace ℝ (Fin n))), IsCompact C →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
            (iteratedFDeriv ℝ m id) atTop C := by
  classical
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := exists_compact_overlap_cutoff
    (hK.image continuous_subtype_val)
    ((hU j).isOpenEmbedding_subtypeVal.isOpenMap _
      (isOpen_overlap hD L he c hc hlower hopen hconn j i)) (image_mono hKoverlap)
  have hcor := eventually_exists_source_chart_correction U hU hD L he c hc hlower
    hopen hconn hsmooth hbound i j hχ hχc hχs
  obtain ⟨a, ha⟩ := hcor.choice
  refine ⟨tsupport χ, hχc.isCompact, hχs, a, ?_, ?_⟩
  · filter_upwards [ha] with k hk
    refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, fun x hx hxK =>
      hk.2.2.2.2.2 x hx (hχone (mem_image_of_mem Subtype.val hxK)), ?_⟩
    intro x hx hagree
    exact source_chart_correction_fixes_agreement U hU hD c hc hlower hopen
      i j k hk.2.2.2.2.1 hx hagree
  · intro m C hC
    exact tendstoUniformlyOn_source_chart_correction_jet U hU hD L he c hc hlower
      hopen hconn hsmooth hbound i j hχ hχc hχs (ha.mono fun _ hk => hk.2.2.2.2.1) m hC

include hD he hc hlower hopen hconn hsmooth in

theorem exists_smooth_source_chart_corrections_on_compact
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {K : Set (Piece U j)} (hK : IsCompact K)
    (hKoverlap : K ⊆ overlap (fun i j => D i j) j i) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      S ⊆ Subtype.val '' overlap (fun i j => D i j) j i ∧
      ∃ a : ℕ → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
        (∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
          (∀ y, y ∉ S → a k y = y) ∧ (a k) '' U j = U j ∧
          ∀ x : Piece U i, x ∈ overlap (fun i j => D i j) i j →
            transition (fun i j => D i j) i j x ∈ K →
            chartParametrization U hU (e k j)
              (a k (transition (fun i j => D i j) i j x)) = e k i x) ∧
        ∀ m (C : Set (EuclideanSpace ℝ (Fin n))), IsCompact C →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
            (iteratedFDeriv ℝ m id) atTop C := by
  obtain ⟨S, hS, hSoverlap, a, ha, hjet⟩ :=
    exists_smooth_relative_source_chart_corrections_on_compact U hU hD L he c hc hlower
      hopen hconn hsmooth hbound i j hK hKoverlap
  refine ⟨S, hS, hSoverlap, a, ?_, hjet⟩
  exact ha.mono fun _ hk => ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1⟩

include hD he hc hlower hopen hconn hsmooth in

theorem exists_smooth_source_chart_corrections_for_compact_pieces
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (i j : ι) {K : Set (Piece U i)} {C : Set (Piece U j)}
    (hK : IsCompact K) (hC : IsCompact C) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      S ⊆ Subtype.val '' overlap (fun i j => D i j) j i ∧
      ∃ a : ℕ → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
        (∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
          (∀ y, y ∉ S → a k y = y) ∧ (a k) '' U j = U j ∧
          ∀ x ∈ K, ∀ y ∈ C, D i j (x, y) = 0 →
            chartParametrization U hU (e k j) (a k y) = e k i x) ∧
        ∀ m B, IsCompact B →
          TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
            (iteratedFDeriv ℝ m id) atTop B := by
  let R : Set (Piece U i × Piece U j) := (K ×ˢ C) ∩ {p | D i j p = 0}
  have hR : IsCompact R := (hK.prod hC).inter_right (isClosed_zero (D i j))
  have hCoverlap : Prod.snd '' R ⊆ overlap (fun i j => D i j) j i := by
    rintro y ⟨⟨x, y⟩, hxy, rfl⟩
    exact ⟨x, (comm hD j i y x).trans hxy.2⟩
  obtain ⟨S, hS, hSoverlap, a, ha, hjet⟩ :=
    exists_smooth_source_chart_corrections_on_compact U hU hD L he c hc hlower
      hopen hconn hsmooth hbound i j (hR.image continuous_snd) hCoverlap
  refine ⟨S, hS, hSoverlap, a, ?_, hjet⟩
  filter_upwards [ha] with k hk
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, ?_⟩
  intro x hx y hy hxy
  obtain ⟨hxo, ht⟩ := (zero_iff_transition hD c hc hlower).mp hxy
  have hyR : y ∈ Prod.snd '' R := ⟨(x, y), ⟨⟨hx, hy⟩, hxy⟩, rfl⟩
  simpa only [ht] using hk.2.2.2.2 x hxo (ht.symm ▸ hyR)

end PoincareConjecture.ChartDistance
