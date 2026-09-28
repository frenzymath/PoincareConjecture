import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.EnclosedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Pullback
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 8

open Set Filter PoincareConjecture Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology Bundle

namespace Poincare.AncientVolume.ScalarRatio

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]

local instance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private theorem coefficients_eqOn
    (g : RiemannianMetric n X)
    {a b : EuclideanSpace ℝ (Fin n) → X} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hab : EqOn a b U) :
    EqOn (g.pullbackCoefficients a) (g.pullbackCoefficients b) U := by
  intro x hx
  have heq : a =ᶠ[𝓝 x] b := hab.eventuallyEq_of_mem (hU.mem_nhds hx)
  simp only [RiemannianMetric.pullbackCoefficients, heq.mfderiv_eq]
  ext v w
  exact congrArg (fun q : X => g.inner q
    (mfderiv (𝓡 n) (𝓡 n) b x v) (mfderiv (𝓡 n) (𝓡 n) b x w)) (hab hx)

private theorem exists_local_convergent_partialDiffeomorph
    (g : RiemannianMetric n X) (gseq : ℕ → RiemannianMetric n X)
    (p : X) (c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (hp : p ∈ c.source)
    (hc : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target)
    (hlim : ∀ m K, IsCompact K → K ⊆ c.target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients c.symm))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients c.symm)) atTop K) :
    ∃ e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) X ∞,
      p ∈ e.target ∧ ∀ m K, IsCompact K → K ⊆ e.source → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients e))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients e)) atTop K := by
  obtain ⟨d, hd, hdc⟩ := hc ⟨c p, c.map_source hp⟩
  let e₀ := d.toOpenPartialHomeomorph.restrOpen c.target c.open_target
  let e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) X ∞ :=
    { toPartialEquiv := e₀.toPartialEquiv
      open_source := e₀.open_source
      open_target := e₀.open_target
      contMDiffOn_toFun := d.contMDiffOn.mono inter_subset_left
      contMDiffOn_invFun := d.symm.contMDiffOn.mono inter_subset_left }
  have hec : EqOn e c.symm e.source := fun _ hx => (hdc hx.1).symm
  have hcp : c p ∈ e.source := ⟨hd, c.map_source hp⟩
  have hep : e (c p) = p := (hec hcp).trans (c.left_inv hp)
  refine ⟨e, hep ▸ e.map_source hcp, ?_⟩
  intro m K hK hKs
  have heq (h : RiemannianMetric n X) := eqOn_iteratedFDeriv_of_isOpen
    e.open_source (coefficients_eqOn h e.open_source hec) m
  exact ((hlim m K hK (hKs.trans inter_subset_right)).congr
    (Eventually.of_forall fun k => (heq (gseq k)).symm.mono hKs)).congr_right
      ((heq g).symm.mono hKs)

theorem exists_countable_convergent_metric_atlas
    [SecondCountableTopology X] [Nonempty X]
    (g : RiemannianMetric n X) (gseq : ℕ → RiemannianMetric n X)
    (hcharts : ∀ p : X, ∃ c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      ∀ m K, IsCompact K → K ⊆ c.target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients c.symm))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients c.symm)) atTop K) :
    ∃ e : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) X ∞,
      (∀ x : X, ∃ i, x ∈ (e i).target) ∧
      ∀ i m K, IsCompact K → K ⊆ (e i).source → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients (e i)))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients (e i))) atTop K := by
  classical
  have hlocal (p : X) :
      ∃ e : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) X ∞,
        p ∈ e.target ∧ ∀ m K, IsCompact K → K ⊆ e.source → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients e))
          (iteratedFDeriv ℝ m (g.pullbackCoefficients e)) atTop K := by
    obtain ⟨c, hp, hc, hlim⟩ := hcharts p
    exact exists_local_convergent_partialDiffeomorph g gseq p c hp hc hlim
  choose d hd hlim using hlocal
  obtain ⟨index, hindex⟩ := isLindelof_univ.indexed_countable_subcover
    (fun p : X => (d p).target) (fun p => (d p).open_target)
    (fun p _ => mem_iUnion.mpr ⟨p, hd p⟩)
  refine ⟨fun i => d (index i), fun x => ?_, fun i => hlim (index i)⟩
  exact mem_iUnion.mp (hindex (mem_univ x))

theorem convergent_metric_charts_on_open
    (g : RiemannianMetric n X) (gseq : ℕ → RiemannianMetric n X)
    (hcharts : ∀ p : X, ∃ c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      ∀ m K, IsCompact K → K ⊆ c.target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients c.symm))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients c.symm)) atTop K)
    (W : TopologicalSpace.Opens X) :
    let gW := g.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) W)
    let gWseq := fun k => (gseq k).pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) W)
    ∀ p : W, ∃ c : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin n)),
      p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      ∀ m K, IsCompact K → K ⊆ c.target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gWseq k).pullbackCoefficients c.symm))
        (iteratedFDeriv ℝ m (gW.pullbackCoefficients c.symm)) atTop K := by
  dsimp only
  intro p
  obtain ⟨c₀, hp₀, hc₀, hlim₀⟩ := hcharts p
  obtain ⟨d, hpd, hlim⟩ := exists_local_convergent_partialDiffeomorph
    g gseq p c₀ hp₀ hc₀ hlim₀
  let e := d.symm.toOpenPartialHomeomorph
  let c := e.subtypeRestr ⟨p⟩
  have hct : c.target ⊆ e.target := e.subtypeRestr_target_subset ⟨p⟩
  have hce : EqOn (Subtype.val ∘ c.symm) d c.target := by
    intro x hx
    exact e.subtypeRestr_symm_apply ⟨p⟩ hx
  have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    intro x hx
    exact (((d.symm.contMDiffOn).contMDiffAt (d.open_target.mem_nhds hx.2)).comp x
      (contMDiff_subtype_val.contMDiffAt)).contMDiffWithinAt
  have hci : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff W c.symm c.target x).mp
    exact ((d.contMDiffOn.mono hct).congr hce) x hx
  let dc : PartialDiffeomorph (𝓡 n) (𝓡 n) W (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := hcs
      contMDiffOn_invFun := hci }
  have hcoeff (h : RiemannianMetric n X) : EqOn
      ((h.pullbackOfLocalDiffeomorph Subtype.val
        (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) W)).pullbackCoefficients c.symm)
      (h.pullbackCoefficients d) c.target := by
    intro x hx
    rw [RiemannianMetric.pullbackCoefficients_eq_of_source_metric h _ Subtype.val
      contMDiff_subtype_val (fun _ _ _ => rfl) c.symm
        (hci.contMDiffAt (c.open_target.mem_nhds hx))]
    exact coefficients_eqOn h c.open_target hce hx
  refine ⟨c, ?_, fun x => ⟨dc.symm, x.property, fun _ _ => rfl⟩, ?_⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hpd
  · intro m K hK hKt
    have heq (h : RiemannianMetric n X) :=
      eqOn_iteratedFDeriv_of_isOpen c.open_target (hcoeff h) m
    exact ((hlim m K hK (hKt.trans hct)).congr
      (Eventually.of_forall fun k => (heq (gseq k)).symm.mono hKt)).congr_right
        ((heq g).symm.mono hKt)

theorem exists_global_enclosed_smooth_limit
    [SecondCountableTopology X] [Nonempty X]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n X) (gseq : ℕ → RiemannianMetric n X)
    (gM : ℕ → RiemannianMetric n M) (A : ℕ → X → M) (q : ℕ → M)
    (hA : ∀ᶠ k in atTop, ContMDiff (𝓡 n) (𝓡 n) ∞ (A k))
    (hmetric : ∀ᶠ k in atTop, ∀ x v w,
      (gseq k).inner x v w = (gM k).inner (A k x)
        (mfderiv (𝓡 n) (𝓡 n) (A k) x v) (mfderiv (𝓡 n) (𝓡 n) (A k) x w))
    (hcharts : ∀ p : X, ∃ c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      ∀ m K, IsCompact K → K ⊆ c.target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gseq k).pullbackCoefficients c.symm))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients c.symm)) atTop K)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r s R : ℝ} (hrs : r < s) (hsR : s < R)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 R)
    (htarget : ∀ k, (Φ k).target = (gM k).ball (q k) R)
    (hradial : ∀ k x, x ∈ Metric.ball 0 R →
      (gM k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (hinside : ∀ᶠ k in atTop, ∀ x : X, A k x ∈ (gM k).ball (q k) r)
    (hBlim : ∀ m K, IsCompact K → K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gM k).pullbackCoefficients (Φ k)))
        (iteratedFDeriv ℝ m (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ)) atTop K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : X → EuclideanSpace ℝ (Fin n),
      ContMDiff (𝓡 n) (𝓡 n) ∞ F ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 n) F x)) ∧
      (∀ x, ∀ v w : TangentSpace (𝓡 n) x,
        inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) =
          g.inner x v w) ∧
      (∀ x, F x ∈ Metric.closedBall 0 r) ∧
      ∀ x, Tendsto (fun k => (Φ (σ k)).symm (A (σ k) x)) atTop (𝓝 (F x)) := by
  classical
  obtain ⟨e, hcover, hlim⟩ := exists_countable_convergent_metric_atlas g gseq hcharts
  have hasource (i : ℕ) : ∀ᶠ k in atTop,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (A k ∘ e i) (e i).source ∧
      ∀ x ∈ (e i).source, (A k ∘ e i) x ∈ (gM k).ball (q k) r := by
    filter_upwards [hA, hinside] with k hkA hki
    exact ⟨hkA.comp_contMDiffOn (e i).contMDiffOn, fun x _ => hki (e i x)⟩
  have hAlim (i m : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hKs : K ⊆ (e i).source) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gM k).pullbackCoefficients (A k ∘ e i)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (e i))) atTop K := by
    apply (hlim i m K hK hKs).congr
    filter_upwards [hA, hmetric] with k hkA hkm
    apply (eqOn_iteratedFDeriv_of_isOpen (e i).open_source ?_ m).mono hKs
    intro x hx
    exact RiemannianMetric.pullbackCoefficients_eq_of_source_metric (gM k) (gseq k) (A k)
      hkA hkm (e i) ((e i).contMDiffOn.contMDiffAt ((e i).open_source.mem_nhds hx))
  obtain ⟨σ, hσ, f, hf, hfrange, hfjet, hfmet, _, hfcompat⟩ :=
    exists_enclosed_smooth_coordinate_limits gM q Φ hrs hsR hsource htarget hradial
      (fun i => (e i).open_source) (fun i k => A k ∘ e i) hasource
      (fun i => g.pullbackCoefficients (e i))
      (fun i x hx => (g.contDiffAt_pullbackCoefficients
        ((e i).contMDiffOn.contMDiffAt ((e i).open_source.mem_nhds hx))).contDiffWithinAt)
      (fun i x hx v hv => g.pos (e i x) _ (by
        intro hz
        apply hv
        apply (((e i).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hx).mfderivToContinuousLinearEquiv
          (by simp)).injective
        change mfderiv (𝓡 n) (𝓡 n) (e i) x v = mfderiv (𝓡 n) (𝓡 n) (e i) x 0
        rw [map_zero]
        convert! hz using 1))
      hAlim hBlim
  obtain ⟨F, hF, hFi, hFm, hFchart⟩ :=
    exists_smooth_isometric_immersion_of_compatible_charts g e hcover f hf
      (fun i j x y hx hy hxy => hfcompat i j x y hx hy
        (Eventually.of_forall fun k => congrArg (A k) hxy)) hfmet
  refine ⟨σ, hσ, F, hF, hFi, hFm, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    have hright : e i ((e i).symm x) = x := (e i).right_inv hi
    have hh := hFchart i ((e i).symm x) ((e i).map_target hi)
    rw [hright] at hh
    rw [hh]
    exact hfrange i ((e i).map_target hi)
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    have hx := (e i).map_target hi
    have ht := (CoordinateTransition.locallyUniformly_of_tendsto_zeroJet
      (e i).open_source (hfjet i 0)).tendsto_at hx
    have hright : e i ((e i).symm x) = x := (e i).right_inv hi
    have hh := hFchart i ((e i).symm x) hx
    rw [hright] at hh
    change Tendsto (fun k => (Φ (σ k)).symm (A (σ k) (e i ((e i).symm x))))
      atTop (𝓝 (f i ((e i).symm x))) at ht
    rw [hright] at ht
    rwa [hh]

end Poincare.AncientVolume.ScalarRatio
