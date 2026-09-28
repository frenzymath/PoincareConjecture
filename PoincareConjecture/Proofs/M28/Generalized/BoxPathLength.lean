import PoincareConjecture.Proofs.M28.Generalized.BoxPathSpeed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Set












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v

namespace PoincareConjecture.M28





theorem continuous_boxTransport_pathELength
    (F : GeneralizedRicciFlowData.{u}) {ι : Type v} (b : ι → F.box_index)
    (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (J : Set ℝ) (hJF : J ⊆ F.interval)
    (hJ : ∀ s ∈ J, ∀ i, s ∈ (F.box (b i)).interval)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContMDiff 𝓘(ℝ) (𝓡 3) 1 γ)
    (himage : MapsTo γ (Icc 0 1) (range (boxEvaluation F b t ht))) :
    Continuous (fun s : J => (F.metric s.val).pathELength
      (boxTransport F b t s.val ht (hJ _ s.property) (hJF s.property) ∘ γ) 0 1) := by
  let speed : J → ℝ → ℝ := fun s v =>
    (F.metric s.val).tangentNorm
      (boxTransport F b t s.val ht (hJ _ s.property) (hJF s.property) (γ v))
      (curveVelocity
        (boxTransport F b t s.val ht (hJ _ s.property) (hJF s.property) ∘ γ) v)
  have hspeed : ContinuousOn (Function.uncurry speed)
      (univ ×ˢ (γ ⁻¹' range (boxEvaluation F b t ht))) :=
    continuousOn_boxTransport_speed F b t ht J hJF hJ γ hγ
  have hcompactSpeed : Continuous (fun z : J × unitInterval => speed z.1 z.2.val) :=
    hspeed.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨mem_univ _, himage z.2.property⟩)
  have hintegral : Continuous (fun s : J => ∫ v : unitInterval, speed s v.val) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    · rw [univ_prod_univ]
      convert hcompactSpeed.continuousOn using 1
      funext z
      rfl
    · simp
  have hlength (s : J) : (F.metric s.val).pathELength
        (boxTransport F b t s.val ht (hJ _ s.property) (hJF s.property) ∘ γ) 0 1 =
      ENNReal.ofReal (∫ v : unitInterval, speed s v.val) := by
    rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
      integral_subtype measurableSet_Icc]
    have hslice : ContinuousOn (speed s) (Icc (0 : ℝ) 1) :=
      hspeed.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun v hv => ⟨mem_univ _, himage hv⟩)
    have hi := hslice.integrableOn_compact (μ := volume) isCompact_Icc
    symm
    exact ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
  exact (ENNReal.continuous_ofReal.comp hintegral).congr (fun s => (hlength s).symm)

end PoincareConjecture.M28
