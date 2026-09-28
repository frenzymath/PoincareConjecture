import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.TimeDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric















set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold Bundle

namespace PoincareConjecture.SpacetimeBounds

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem spatial_fderiv_eq {f : ℝ × V → E} {t : ℝ} {x : V}
    (hf : DifferentiableAt ℝ f (t, x)) :
    fderiv ℝ (fun y => f (t, y)) x =
      (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
  exact (hf.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

theorem contDiffOn_spatialFDeriv {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : IsOpen J) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => fderiv ℝ (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  have hd := (hf.fderiv_of_isOpen (hJ.prod hU) (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ V))
  apply hd.congr
  intro z hz
  exact spatial_fderiv_eq ((hf.contDiffAt ((hJ.prod hU).mem_nhds hz)).differentiableAt
    (by simp))



theorem contDiffOn_timeDeriv {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : IsOpen J) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => deriv (fun t => f (t, z.2)) z.1)
      (J ×ˢ U) := by
  have hd := (hf.fderiv_of_isOpen (hJ.prod hU) (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := ((1 : ℝ), (0 : V))))
  apply hd.congr
  intro z hz
  exact (((hf.contDiffAt ((hJ.prod hU).mem_nhds hz)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

theorem hasDerivAt_spatialFDeriv {f : ℝ × V → E} {k : V → E}
    {J : Set ℝ} {U : Set V} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    (hJ : IsOpen J) (hU : IsOpen U) {t : ℝ} (ht : t ∈ J)
    (hk : ∀ x ∈ U, HasDerivAt (fun s => f (s, x)) (k x) t)
    {y : V} (hy : y ∈ U) :
    HasDerivAt (fun s => fderiv ℝ (fun x => f (s, x)) y) (fderiv ℝ k y) t := by
  have hsmooth : ContDiffAt ℝ 2 f (t, y) :=
    (contDiffOn_infty.mp hf 2).contDiffAt ((hJ.prod hU).mem_nhds ⟨ht, hy⟩)
  have hD := ((hsmooth.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have htline : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : V)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hd := (hD.comp_hasDerivAt t htline).clm_comp
    (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ V))
  have heq : (fun s => fderiv ℝ (fun x => f (s, x)) y) =ᶠ[𝓝 t]
      (fun s => (fderiv ℝ f (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ V)) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact spatial_fderiv_eq
      ((hf.contDiffAt ((hJ.prod hU).mem_nhds ⟨hs, hy⟩)).differentiableAt (by simp))
  have hkEq : k =ᶠ[𝓝 y] (fun x => fderiv ℝ f (t, x) (1, 0)) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    have hfx : DifferentiableAt ℝ f (t, x) :=
      (hf.contDiffAt ((hJ.prod hU).mem_nhds ⟨ht, hx⟩)).differentiableAt (by simp)
    exact (hk x hx).unique (hfx.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)))
  have hspace := hD.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have hK := hspace.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : V)) y)
  dsimp only [Function.comp_def] at hK
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  rw [hkEq.fderiv_eq, hK.fderiv]
  ext v
  simpa using (hsmooth.isSymmSndFDerivAt (by norm_num)).eq
    ((1 : ℝ), (0 : V)) ((0 : ℝ), v)

theorem contDiffOn_spatialJet {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : IsOpen J) (hU : IsOpen U) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => iteratedFDeriv ℝ m (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  induction m with
  | zero =>
      let e := (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv
      exact e.toContinuousLinearMap.contDiff.comp_contDiffOn hf
  | succ m ih =>
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) E).symm
      convert! e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
        (contDiffOn_spatialFDeriv ih hJ hU) using 1


theorem hasDerivAt_spatialJet {f : ℝ × V → E} {k : V → E}
    {J : Set ℝ} {U : Set V} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U))
    (hJ : IsOpen J) (hU : IsOpen U) {t : ℝ} (ht : t ∈ J)
    (hk : ∀ x ∈ U, HasDerivAt (fun s => f (s, x)) (k x) t)
    (m : ℕ) {y : V} (hy : y ∈ U) :
    HasDerivAt (fun s => iteratedFDeriv ℝ m (fun x => f (s, x)) y)
      (iteratedFDeriv ℝ m k y) t := by
  induction m generalizing y with
  | zero =>
      let e := (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv
      exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hk y hy)
  | succ m ih =>
      have hd := hasDerivAt_spatialFDeriv (contDiffOn_spatialJet hf hJ hU m)
        hJ hU ht (fun x hx => ih hx) hy
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) E).symm
      convert! e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
        using 1

end PoincareConjecture.SpacetimeBounds

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem hasDerivAt_spatialJet_pullbackCoefficients_apply (F : RicciFlow n M J)
    (hJ : IsOpen J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) (m : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (u v : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => iteratedFDeriv ℝ m
      (fun y => (F.metric s).pullbackCoefficients e y u v) x)
      (iteratedFDeriv ℝ m (fun y => -2 * (F.connection t).ricci (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v)) x) t := by
  apply SpacetimeBounds.hasDerivAt_spatialJet
    (((F.contDiffOn_pullbackCoefficients hJ hU he).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const) hJ hU ht _ m hx
  intro y _
  exact (F.equation t ht (e y) (mfderiv (𝓡 n) (𝓡 n) e y u)
    (mfderiv (𝓡 n) (𝓡 n) e y v)).hasDerivAt (hJ.mem_nhds ht)

end PoincareConjecture.RicciFlow
