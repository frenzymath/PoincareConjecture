import PoincareConjecture.Proofs.M62.Mathlib.FlatCircleCharts
import PoincareConjecture.Proofs.M01.NormalizationMetric
import PoincareConjecture.Proofs.M01.ConnectionExistence
import PoincareConjecture.Proofs.M04.MetricPairings
import PoincareConjecture.Definitions.M62Geometry
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

set_option maxHeartbeats 800000 in



theorem exists_circleMetric_of_flatQuotient {p : ℝ}
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle p)]
    [IsManifold (𝓡 1) ∞ (AddCircle p)]
    (e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hq : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞
      (fun s : ℝ => (s : AddCircle p)))
    (hd : ∀ s : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun r : ℝ => (r : AddCircle p)) s e.toContinuousLinearMap) :
    ∃ g : RiemannianMetric 1 (AddCircle p),
      ∀ (q : AddCircle p) (V W : TangentSpace (𝓡 1) q),
        g.inner q V W = e.symm V * e.symm W := by
  let E := EuclideanSpace ℝ (Fin 1)
  let Q : (q : AddCircle p) → TangentSpace (𝓡 1) q →L[ℝ]
      TangentSpace (𝓡 1) q →L[ℝ] ℝ := fun _ =>
    (e.symm.toContinuousLinearMap.precomp ℝ).comp
      ((ContinuousLinearMap.mul ℝ ℝ).comp e.symm.toContinuousLinearMap)
  have hQ (q : AddCircle p) (V W : TangentSpace (𝓡 1) q) :
      Q q V W = e.symm V * e.symm W := rfl
  have hpos (q : AddCircle p) (V : TangentSpace (𝓡 1) q) (hV : V ≠ 0) :
      0 < Q q V V := by
    rw [hQ]
    apply mul_self_pos.mpr
    exact fun h => hV (e.symm.injective (h.trans (map_zero e.symm).symm))
  refine ⟨{
    inner := Q
    symm := fun q V W => by rw [hQ, hQ, mul_comm]
    pos := hpos
    isVonNBounded := fun q => m01_isVonNBounded_of_posDef (F := E) (Q q) (hpos q)
    contMDiff := ?_
  }, hQ⟩
  intro q
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
  let σ := (hq s).localInverse
  have hs : (s : AddCircle p) ∈ σ.source := (hq s).localInverse_mem_source
  have hσ (y : AddCircle p) (hy : y ∈ σ.source) :
      ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ σ y :=
    ((hq s).contmdiffOn_localInverse y hy).contMDiffAt (σ.open_source.mem_nhds hy)
  have hσd (y : AddCircle p) (hy : y ∈ σ.source) :
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ y = e.symm.toContinuousLinearMap := by
    have heq : (fun z => ((σ z : ℝ) : AddCircle p)) =ᶠ[𝓝 y] id := by
      filter_upwards [σ.open_source.mem_nhds hy] with z hz
      exact (hq s).localInverse_right_inv hz
    have hid := heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 1)
    rw [mfderiv_id] at hid
    have hc := mfderiv_comp (f := σ) (g := fun r : ℝ => (r : AddCircle p)) y
      (hd (σ y)).mdifferentiableAt ((hσ y hy).mdifferentiableAt (by simp))
    rw [(hd (σ y)).mfderiv] at hc
    ext v
    apply e.injective
    have hv := congrArg (fun L : E →L[ℝ] E => L v) (hc.symm.trans hid)
    change e (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ y v) = v at hv
    change e (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) σ y v) = e (e.symm v)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hv
  let τ := trivializationAt E (TangentSpace (𝓡 1) : AddCircle p → Type _) (s : AddCircle p)
  have hτ : (s : AddCircle p) ∈ τ.baseSet := mem_baseSet_trivializationAt E _ _
  let S : E → (y : AddCircle p) → TangentSpace (𝓡 1) y := fun v y => τ.symmL ℝ y v
  have hS (v : E) : ContMDiffAt (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, E)) ∞
      (fun y : AddCircle p => TotalSpace.mk' E y (S v y)) (s : AddCircle p) := by
    rw [τ.contMDiffAt_section_iff hτ]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [τ.open_baseSet.mem_nhds hτ] with y hy
    simpa only [S, Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd (τ.apply_mk_symm hy v)
  have hscalar (v : E) : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun y : AddCircle p => e.symm (S v y)) (s : AddCircle p) := by
    have h := ((hσ (s : AddCircle p) hs).mfderiv_const (m := ∞)
      (by simp)).clm_apply_of_inCoordinates (hS v) (hσ (s : AddCircle p) hs)
    have h' := (contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℝ 𝓘(ℝ, ℝ) _).comp
      (s : AddCircle p) h
    apply h'.congr_of_eventuallyEq
    filter_upwards [σ.open_source.mem_nhds hs] with y hy
    exact (congrArg (fun L => L (S v y)) (hσd y hy)).symm
  rw [contMDiffAt_section]
  apply M04.contMDiffAt_clm_of_apply
  intro v
  apply M04.contMDiffAt_clm_of_apply
  intro w
  apply ((hscalar v).mul (hscalar w)).congr_of_eventuallyEq
  filter_upwards [τ.open_baseSet.mem_nhds hτ] with y hy
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hy hy (mem_univ y)]
  simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_apply]
  change e.symm (τ.symm y v) * e.symm (τ.symm y w) =
    e.symm (τ.symmL ℝ y v) * e.symm (τ.symmL ℝ y w)
  rw [Trivialization.symmL_apply τ hy, Trivialization.symmL_apply τ hy]



theorem nonempty_circleGeometry {p : ℝ} (hp : 0 < p) :
    Nonempty (CircleGeometry p) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
  obtain ⟨C, hC, hq, hd⟩ := AddCircle.exists_flatChartedSpace e hp
  let : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle p) := C
  let : IsManifold (𝓡 1) ∞ (AddCircle p) := hC
  obtain ⟨g, hg⟩ := exists_circleMetric_of_flatQuotient e hq hd
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  refine ⟨{
    positive := hp
    chartedSpace := C
    isManifold := hC
    quotient_smooth := hq.contMDiff
    quotient_local_diffeomorph := hq
    metric := g
    connection := D
    metric_quotient := ?_
    frame := fun _ => e 1
    frame_quotient := ?_ }⟩
  · intro s v w
    rw [hg, (hd s).mfderiv]
    change e.symm (e v) * e.symm (e w) = v * w
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  · intro s
    rw [(hd s).mfderiv]
    rfl

end PoincareConjecture.M62
