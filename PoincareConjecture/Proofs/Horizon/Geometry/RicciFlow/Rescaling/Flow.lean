import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Bundle
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J K : Set ℝ}

noncomputable def parabolicRescale
    (F : RicciFlow n M J) (c : ℝ) (hc : 0 < c) (τ : ℝ)
    (hKJ : MapsTo (fun s : ℝ ↦ τ + s / c) K J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) : RicciFlow n M K where
  metric s := rescaledMetric (F.metric (τ + s / c)) c hc
  connection s := rescaledMetric_connection (F.metric (τ + s / c))
    (F.connection (τ + s / c)) c hc
  interval := hK
  nontrivial := hne
  smooth := by
    have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ p.1) (K ×ˢ univ) := contMDiffOn_fst
    have hcst : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun _ : ℝ × M ↦ c⁻¹) (K ×ˢ univ) := contMDiffOn_const
    have htime : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × M ↦ (τ + p.1 / c, p.2)) (K ×ˢ univ) := by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, div_eq_mul_inv,
        mul_comm c⁻¹] using
        ((contMDiffOn_const (c := τ)).add (hcst.smul hf)).prodMk
          (contMDiffOn_snd (M := ℝ) (N := M))
    have hs := F.smooth.comp htime (fun p hp ↦ ⟨hKJ hp.1, hp.2⟩)
    intro p hp
    have hsp := hs p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at hsp ⊢
    refine ⟨hsp.1, ?_⟩
    let E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
    let : NormedAddCommGroup E := inferInstanceAs
      (NormedAddCommGroup
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    let : NormedSpace ℝ E := inferInstanceAs
      (NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    let V := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let (x : M) : ContinuousAdd (TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
      inferInstanceAs (ContinuousAdd (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    let : VectorBundle ℝ E V := inferInstanceAs
      (VectorBundle ℝ
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ))
    let e := trivializationAt E V p.2
    let : e.IsLinear ℝ := trivialization_linear ℝ (F := E) (E := V) e
    have he : ∀ᶠ q : ℝ × M in 𝓝[K ×ˢ univ] p, q.2 ∈ e.baseSet :=
      continuous_snd.continuousWithinAt (e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E V p.2))
    have hconst : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun _ : ℝ × M ↦ c) (K ×ˢ univ) p := contMDiffWithinAt_const
    apply (hconst.smul hsp.2).congr_of_eventuallyEq
    · filter_upwards [he] with q hq
      exact ((e.linear ℝ hq).map_smul c
        ((F.metric (τ + q.1 / c)).inner q.2))
    · exact ((e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt E V p.2)).map_smul c
        ((F.metric (τ + p.1 / c)).inner p.2))
  equation := by
    intro s hs x u v
    have hinner : HasDerivWithinAt (fun r : ℝ ↦ τ + r / c) c⁻¹ K s := by
      simpa only [one_div, id_eq] using
        (((hasDerivAt_id s).div_const c).const_add τ).hasDerivWithinAt
    have houter := F.equation (τ + s / c) (hKJ hs) x u v
    have hcomp := (houter.comp s hinner hKJ).const_mul c
    simpa only [Function.comp_def, rescaledMetric_inner, rescaledMetric_ricci,
      show c * (-2 * (F.connection (τ + s / c)).ricci x u v * c⁻¹) =
        -2 * (F.connection (τ + s / c)).ricci x u v by field_simp] using hcomp

theorem parabolicRescale_metric
    (F : RicciFlow n M J) (c : ℝ) (hc : 0 < c) (τ : ℝ)
    (hKJ : MapsTo (fun s : ℝ ↦ τ + s / c) K J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) (s : ℝ) :
    (F.parabolicRescale c hc τ hKJ hK hne).metric s =
      rescaledMetric (F.metric (τ + s / c)) c hc := rfl

end PoincareConjecture.RicciFlow
