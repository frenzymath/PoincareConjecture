import PoincareConjecture.Statements.M12MovingGaugeTheory
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.LinearAlgebra.Basis.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

private theorem isOpenMap_of_map_nhds_eq {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] {f : M → N}
    (h : ∀ x, map f (𝓝 x) = 𝓝 (f x)) : IsOpenMap f := by
  intro U hU
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro y ⟨x, hx, rfl⟩
  rw [← h x]
  exact image_mem_map (hU.mem_nhds hx)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_smooth_local_left_inverse
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hbij : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ∃ g : N → M, ContMDiffAt (𝓡 n) (𝓡 n) ∞ g (f x) ∧
      ∀ᶠ z in 𝓝 x, g (f z) = z := by
  let c := extChartAt (𝓡 n) x
  let d := extChartAt (𝓡 n) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓡 n) x f
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let i := hF.localInverse hdF (by simp)
  have hi : ContDiffAt ℝ ∞ i (F (c x)) := hF.to_localInverse hdF (by simp)
  have hix : i (F (c x)) = c x := hF.localInverse_apply_image hdF (by simp)
  have hFx : F (c x) = d (f x) := by simp [F, c, d, writtenInExtChartAt]
  have hil : ∀ᶠ z in 𝓝 (c x), i (F z) = z :=
    (hF.hasStrictFDerivAt' hdF (by simp)).eventually_left_inverse
  let g : N → M := fun y ↦ c.symm (i (d y))
  have hg : ContMDiffAt (𝓡 n) (𝓡 n) ∞ g (f x) := by
    have hd : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d (f x) := contMDiffAt_extChartAt
    have hi' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ i (d (f x)) := by
      rw [← hFx]
      exact hi.contMDiffAt
    have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (i (d (f x))) := by
      rw [← hFx, hix]
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds (mem_extChartAt_target x))
    exact hcs.comp (f x) (hi'.comp (f x) hd)
  have hc : ContinuousAt c x := continuousAt_extChartAt x
  have heq : ∀ᶠ z in 𝓝 x, g (f z) = z := by
    filter_upwards [hc.tendsto.eventually hil,
      (isOpen_extChartAt_source (I := 𝓡 n) x).mem_nhds (mem_extChartAt_source x)]
      with z hzi hzc
    dsimp [g]
    have hFz : F (c z) = d (f z) := by
      simp only [F, writtenInExtChartAt, Function.comp_apply]
      rw [c.left_inv hzc]
    rw [← hFz, hzi, c.left_inv hzc]
  exact ⟨g, hg, heq⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_smooth_local_left_inverse_model
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]
    {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ f x)
    (hbij : Function.Bijective
      (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x)) :
    ∃ g : N → M, ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞ g (f x) ∧
      ∀ᶠ z in 𝓝 x, g (f z) = z := by
  let c := extChartAt (𝓡 n) x
  let d := extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x f
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x =
      fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F
      (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let i := hF.localInverse hdF (by simp)
  have hi : ContDiffAt ℝ ∞ i (F (c x)) := hF.to_localInverse hdF (by simp)
  have hix : i (F (c x)) = c x := hF.localInverse_apply_image hdF (by simp)
  have hFx : F (c x) = d (f x) := by simp [F, c, d, writtenInExtChartAt]
  have hil : ∀ᶠ z in 𝓝 (c x), i (F z) = z :=
    (hF.hasStrictFDerivAt' hdF (by simp)).eventually_left_inverse
  let g : N → M := fun y ↦ c.symm (i (d y))
  have hg : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞ g (f x) := by
    have hd : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ d (f x) :=
      contMDiffAt_extChartAt
    have hi' : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ i (d (f x)) := by
      rw [← hFx]
      exact hi.contMDiffAt
    have hcs : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
        c.symm (i (d (f x))) := by
      rw [← hFx, hix]
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds (mem_extChartAt_target x))
    exact hcs.comp (f x) (hi'.comp (f x) hd)
  have hc : ContinuousAt c x := continuousAt_extChartAt x
  have heq : ∀ᶠ z in 𝓝 x, g (f z) = z := by
    filter_upwards [hc.tendsto.eventually hil,
      (isOpen_extChartAt_source (I := 𝓡 n) x).mem_nhds (mem_extChartAt_source x)]
      with z hzi hzc
    dsimp [g]
    have hFz : F (c z) = d (f z) := by
      simp only [F, writtenInExtChartAt, Function.comp_apply]
      rw [c.left_inv hzc]
    rw [← hFz, hzi, c.left_inv hzc]
  exact ⟨g, hg, heq⟩

theorem isLocalDiffeomorph_of_contMDiff_mfderiv_bijective
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [Nonempty M]
    {f : M → N} (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hinj : Function.Injective f)
    (hbij : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f := by
  have hmap : ∀ x, map f (𝓝 x) = 𝓝 (f x) := fun x ↦
    Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective (hf x) (hbij x)
  have hopen : IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuous hinj
      (isOpenMap_of_map_nhds_eq hmap)
  have hlocal : IsLocalHomeomorph f := hopen.isLocalHomeomorph
  intro x
  obtain ⟨e, hx, he⟩ := hlocal x
  have hinv : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.invFun e.target := by
    intro y hy
    have hz : e.invFun y ∈ e.source := e.map_target hy
    have hfy : f (e.invFun y) = y := by
      rw [he]
      exact e.right_inv hy
    have hgi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (Function.invFun f) y := by
      rw [← hfy]
      exact Poincare.contMDiffAt_of_local_left_inverse (hf (e.invFun y))
        (hbij (e.invFun y)) (Eventually.of_forall (Function.leftInverse_invFun hinj))
    have heq : e.invFun =ᶠ[𝓝 y] Function.invFun f := by
      filter_upwards [e.open_target.mem_nhds hy] with y' hy'
      apply hinj
      have hleft : f (e.invFun y') = y' := by
        rw [he]
        exact e.right_inv hy'
      exact hleft.trans (Function.invFun_eq ⟨e.invFun y', hleft⟩).symm
    exact hgi.congr_of_eventuallyEq heq |>.contMDiffWithinAt
  refine ⟨{ toPartialEquiv := e.toPartialEquiv
            open_source := e.open_source
            open_target := e.open_target
            contMDiffOn_toFun := ?_
            contMDiffOn_invFun := hinv }, hx, ?_⟩
  · exact hf.contMDiffOn.congr fun z _z ↦ (congr_fun he z).symm
  · exact fun z _z ↦ congr_fun he z

theorem movingGaugeSliceMap_comp_inclusion
    (e : MovingSpacetimeGauge F T C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s) (t : T.Point) :
    (Subtype.val : (S t.val).Point → F.Point) ∘ movingGaugeSliceMap e S t =
      (fun x : C ↦ e.toSpacetime (t, x)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem movingGaugeSliceMap_contMDiffAt
    (e : MovingSpacetimeGauge F T C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s)
    (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (movingGaugeSliceMap e S t) x := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t.val).Point :=
    (S t.val).chartedSpace
  letI : IsManifold (𝓡 n) ∞ (S t.val).Point := (S t.val).isManifold
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let q : (S t.val).Point := movingGaugeSliceMap e S t x
  let p : F.Point := q.val
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) q) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) q) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup (TangentSpace (spacetimeModel n) p) :=
    inferInstanceAs
      (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (spacetimeModel n) p) :=
    inferInstanceAs
      (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  let D : TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (spacetimeModel n) p :=
    mfderiv (𝓡 n) (spacetimeModel n)
      (Subtype.val : (S t.val).Point → F.Point) q
  have hDinj : Function.Injective D := (S t.val).inclusion_differential_injective q
  letI : FiniteDimensional ℝ (TangentSpace (spacetimeModel n) p) := by
    exact ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).finiteDimensional_of_finite
  obtain ⟨P₀, hP₀⟩ := D.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hDinj)
  let P : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    P₀.toContinuousLinearMap
  have hP : P.comp D =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearMap.ext
    intro v
    change P₀ (D v) = v
    exact congrArg (fun f ↦ f v) hP₀
  let h : (S t.val).Point → EuclideanSpace ℝ (Fin n) :=
    fun z ↦ P (extChartAt (spacetimeModel n) p z.val)
  have hinc : ContMDiffAt (𝓡 n) (spacetimeModel n) ∞
      (Subtype.val : (S t.val).Point → F.Point) q :=
    (S t.val).inclusion_smooth q
  have hchart : ContMDiffAt (spacetimeModel n)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n))) ∞
      (extChartAt (spacetimeModel n) p) p := contMDiffAt_extChartAt
  have hh : ContMDiffAt (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ h q := by
    have hcomp := hchart.comp q hinc
    have hPcont : ContMDiffAt
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ P
        (extChartAt (spacetimeModel n) p q.val) := P.contMDiffAt
    simpa [h, Function.comp_def] using hPcont.comp q hcomp
  have hinc' := hinc.mdifferentiableAt (by simp)
  have hchart' := hchart.mdifferentiableAt (by simp)
  have hcomp' := mfderiv_comp q hchart' hinc'
  have hPcont : ContMDiffAt
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ P
      (extChartAt (spacetimeModel n) p q.val) := P.contMDiffAt
  have hP' := hPcont.mdifferentiableAt
    (x := extChartAt (spacetimeModel n) p q.val) (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hchart_comp : ContMDiffAt (𝓡 n)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n))) ∞
      (extChartAt (spacetimeModel n) p ∘
        (Subtype.val : (S t.val).Point → F.Point)) q := by
    simpa [p] using hchart.comp q hinc
  have hchart_comp' := hchart_comp.mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have houter := mfderiv_comp q hP' hchart_comp'
  have hmf :
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (h q)).toContinuousLinearMap.comp
          (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) h q) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (h q)).toContinuousLinearMap.comp
        (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (P ∘ (extChartAt (spacetimeModel n) p ∘
            (Subtype.val : (S t.val).Point → F.Point))) q) = _
    rw [houter]
    have hmfP : mfderiv
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) P
        (extChartAt (spacetimeModel n) p q.val) = P := by
      rw [mfderiv, if_pos (hPcont.mdifferentiableAt (by simp))]
      simp [ContinuousLinearMap.fderiv]
    have hbase :
        (extChartAt (spacetimeModel n) p ∘
            (Subtype.val : (S t.val).Point → F.Point)) q =
          extChartAt (spacetimeModel n) p q.val := rfl
    rw [hbase, hmfP]
    rw [hcomp', mfderiv_extChartAt_self]
    apply ContinuousLinearMap.ext
    intro v
    change P (D v) = v
    have hv := congrArg (fun L ↦ L v) hP
    have hid : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v = v := rfl
    have hv' : P (D v) = (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v := by
      exact hv
    exact hv'.trans hid
  have hbij : Function.Bijective
      (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) h q) := by
    let E := NormedSpace.fromTangentSpace (𝕜 := ℝ) (h q)
    constructor
    · intro v w hvw
      have hv := congrArg (fun L ↦ L v) hmf
      have hw := congrArg (fun L ↦ L w) hmf
      change E (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) h q v) = v at hv
      change E (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) h q w) = w at hw
      rw [hvw] at hv
      exact (hw.symm.trans hv).symm
    · intro w
      refine ⟨E.symm w, ?_⟩
      apply E.injective
      have hw := congrArg (fun L ↦ L (E.symm w)) hmf
      change E (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) h q (E.symm w)) =
        E (E.symm w) at hw
      exact hw
  obtain ⟨g, hg, hleft⟩ := exists_smooth_local_left_inverse_model hh hbij
  let k : C → EuclideanSpace ℝ (Fin n) :=
    fun y ↦ P (extChartAt (spacetimeModel n) p (e.toSpacetime (t, y)))
  have he_t : ContMDiffAt (𝓡 n) (spacetimeModel n) ∞
      (fun y : C ↦ e.toSpacetime (t, y)) x := by
    exact (e.smooth (t, x)).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  have hk : ContMDiffAt (𝓡 n) (𝓡 n) ∞ k x := by
    have hcomp := hchart.comp x he_t
    have hPcont : ContMDiffAt
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ P
        (extChartAt (spacetimeModel n) p (e.toSpacetime (t, x))) := by
      simpa [p] using P.contMDiffAt
    simpa [k, Function.comp_def] using hPcont.comp x hcomp
  have hfcont : ContinuousAt (movingGaugeSliceMap e S t) x := by
    have hcont : Continuous (movingGaugeSliceMap e S t) := by
      apply continuous_induced_rng.mpr
      change Continuous ((Subtype.val : (S t.val).Point → F.Point) ∘
        movingGaugeSliceMap e S t)
      rw [movingGaugeSliceMap_comp_inclusion]
      exact (e.embedding.comp (isEmbedding_prodMkRight t)).continuous
    exact hcont.continuousAt
  have hleft' : ∀ᶠ y in 𝓝 x,
      g (k y) = movingGaugeSliceMap e S t y := by
    filter_upwards [hfcont.preimage_mem_nhds hleft] with y hy
    have heq : h (movingGaugeSliceMap e S t y) = k y := by
      rfl
    rw [← heq]
    exact hy
  have hcomp := hg.comp x hk
  have hleftEq :
      (fun y : C ↦ g (k y)) =ᶠ[𝓝 x] movingGaugeSliceMap e S t := by
    filter_upwards [hleft'] with y hy
    exact hy
  exact hcomp.congr_of_eventuallyEq hleftEq.symm

theorem movingGaugeSliceMap_tangent_eq
    (e : MovingSpacetimeGauge F T C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s)
    (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) (u : TangentSpace (𝓡 n) x) :
    (S t.val).tangentEquiv (movingGaugeSliceMap e S t x)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u) =
        G.spatialTangentEquiv t x u := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t.val).Point :=
    (S t.val).chartedSpace
  letI : IsManifold (𝓡 n) ∞ (S t.val).Point := (S t.val).isManifold
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup
      (TangentSpace (𝓡 n) (movingGaugeSliceMap e S t x)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ
      (TangentSpace (𝓡 n) (movingGaugeSliceMap e S t x)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have hsmooth : ContMDiff (𝓡 n) (𝓡 n) ∞ (movingGaugeSliceMap e S t) :=
    fun y ↦ movingGaugeSliceMap_contMDiffAt e S G t y
  have hslice := hsmooth.mdifferentiableAt (x := x) (by simp)
  have hincl : MDifferentiableAt (𝓡 n) (spacetimeModel n)
      (Subtype.val : (S t.val).Point → F.Point)
      (movingGaugeSliceMap e S t x) :=
    (S t.val).inclusion_smooth.mdifferentiableAt (x := movingGaugeSliceMap e S t x)
      (by simp)
  have hcomp := mfderiv_comp x hincl hslice
  have hcomp' := congrArg (fun L => L u) hcomp
  have hspatial := G.spatialTangentEquiv_eq t x u
  have hval := (S t.val).tangentEquiv_eq (movingGaugeSliceMap e S t x)
    (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u)
  have hcomp'' :
      mfderiv (𝓡 n) (spacetimeModel n)
          (Subtype.val : (S t.val).Point → F.Point)
          (movingGaugeSliceMap e S t x)
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u) =
        mfderiv (𝓡 n) (spacetimeModel n)
          (fun y : C ↦ e.toSpacetime (t, y)) x u := by
    rw [movingGaugeSliceMap_comp_inclusion e S t] at hcomp'
    change
      mfderiv (𝓡 n) (spacetimeModel n) (fun y : C ↦ e.toSpacetime (t, y)) x u =
        mfderiv (𝓡 n) (spacetimeModel n)
          (Subtype.val : (S t.val).Point → F.Point)
          (movingGaugeSliceMap e S t x)
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u) at hcomp'
    exact hcomp'.symm
  apply Subtype.ext
  rw [hval]
  simpa [hspatial] using hcomp''

theorem movingGaugeSliceMap_localDiffeomorph
    (e : MovingSpacetimeGauge F T C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s)
    (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (movingGaugeSliceMap e S t) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S t.val).Point :=
    (S t.val).chartedSpace
  letI : IsManifold (𝓡 n) ∞ (S t.val).Point := (S t.val).isManifold
  by_cases hC : Nonempty C
  · letI : Nonempty C := hC
    apply isLocalDiffeomorph_of_contMDiff_mfderiv_bijective
      (fun y ↦ movingGaugeSliceMap_contMDiffAt e S G t y)
    · intro a b hab
      have hval := congrArg (fun z : (S t.val).Point ↦ z.val) hab
      have hsp : e.toSpacetime (t, a) = e.toSpacetime (t, b) := by
        simpa [movingGaugeSliceMap] using hval
      exact congrArg Prod.snd (e.embedding.injective hsp)
    · intro y
      letI : NormedAddCommGroup (TangentSpace (𝓡 n) y) :=
        inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
      letI : NormedSpace ℝ (TangentSpace (𝓡 n) y) :=
        inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
      letI : NormedAddCommGroup
          (TangentSpace (𝓡 n) (movingGaugeSliceMap e S t y)) :=
        inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
      letI : NormedSpace ℝ
          (TangentSpace (𝓡 n) (movingGaugeSliceMap e S t y)) :=
        inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
      have hi : Function.Injective
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) y) := by
        intro u v huv
        have htan :
            (S t.val).tangentEquiv (movingGaugeSliceMap e S t y)
                (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) y u) =
              (S t.val).tangentEquiv (movingGaugeSliceMap e S t y)
                (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) y v) :=
          congrArg
            (fun z : TangentSpace (𝓡 n) (movingGaugeSliceMap e S t y) ↦
              (S t.val).tangentEquiv (movingGaugeSliceMap e S t y) z) huv
        have hG : G.spatialTangentEquiv t y u =
            G.spatialTangentEquiv t y v := by
          exact (movingGaugeSliceMap_tangent_eq e S G t y u).symm.trans
            (htan.trans (movingGaugeSliceMap_tangent_eq e S G t y v))
        exact (G.spatialTangentEquiv t y).injective hG
      letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) := by
        unfold TangentSpace
        exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
      letI : FiniteDimensional ℝ
          (TangentSpace (𝓡 n) (movingGaugeSliceMap e S t y)) := by
        unfold TangentSpace
        exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
      have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) y) =
          Module.finrank ℝ
            (TangentSpace (𝓡 n) (movingGaugeSliceMap e S t y)) := by
        unfold TangentSpace
        rfl
      exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩
  · intro y
    exact (hC ⟨y⟩).elim

theorem movingGaugeSliceMap_metric_eq
    (e : MovingSpacetimeGauge F T C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s)
    (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x)
    (htangent :
      (S t.val).tangentEquiv (movingGaugeSliceMap e S t x)
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u) =
        G.spatialTangentEquiv t x u)
    (htangent' :
      (S t.val).tangentEquiv (movingGaugeSliceMap e S t x)
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x v) =
        G.spatialTangentEquiv t x v) :
    (S t.val).metricOnPoints.inner (movingGaugeSliceMap e S t x)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x v) =
      (G.metric t.val).inner x u v := by
  rw [(S t.val).metric_eq]
  rw [htangent, htangent']
  exact (G.metric_eq t x u v).symm

end

end PoincareConjecture
