import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.LoopValueCongruence

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

noncomputable section

universe u v

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem contMDiffOn_m59PairInterpolation (C : ℝ × (M × M) → M) (t : ℝ)
    (delta gamma : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, delta z, gamma z)) :
    ContMDiffOn (𝓡 2) (𝓡 3) 1
      (fun w => C (t, delta.extension (radialNormalization w),
        gamma.extension (radialNormalization w))) loopAnnulus := by
  intro w hw
  have hw0 : w ≠ 0 := by
    intro hzero
    have hp := hw.1
    norm_num [hzero] at hp
  let z : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
  have hd : ContMDiffAt (𝓡 2) (𝓡 3) 1 (delta.extension ∘ radialNormalization) w :=
    (contMDiffOn_radial_extension delta w hw).contMDiffAt (isOpen_loopAnnulus.mem_nhds hw)
  have hg : ContMDiffAt (𝓡 2) (𝓡 3) 1 (gamma.extension ∘ radialNormalization) w :=
    (contMDiffOn_radial_extension gamma w hw).contMDiffAt (isOpen_loopAnnulus.mem_nhds hw)
  exact ((hC z).comp_of_eq (contMDiffAt_const.prodMk (hd.prodMk hg)) (by
    change (t, delta.extension z.val, gamma.extension z.val) = (t, delta z, gamma z)
    rw [delta.boundary, gamma.boundary])).contMDiffWithinAt

def m59PairInterpolationLoop (C : ℝ × (M × M) → M) (t : ℝ)
    (delta gamma : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, delta z, gamma z)) : C1FreeLoopSpace (M := M) :=
  loopOfExtension (fun w => C (t, delta.extension (radialNormalization w),
    gamma.extension (radialNormalization w))) (contMDiffOn_m59PairInterpolation C t delta gamma hC)

theorem m59PairInterpolationLoop_apply (C : ℝ × (M × M) → M) (t : ℝ)
    (delta gamma : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, delta z, gamma z)) (z : LoopCircle) :
    m59PairInterpolationLoop C t delta gamma hC z = C (t, delta z, gamma z) := by
  change C (t, delta.extension (radialNormalization z.val),
    gamma.extension (radialNormalization z.val)) = _
  rw [radialNormalization_of_norm_eq_one z.property, delta.boundary, gamma.boundary]

theorem m59PairInterpolationLoop_tangent (C : ℝ × (M × M) → M) (t : ℝ)
    (delta gamma : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, delta z, gamma z)) (z : LoopCircle) :
    c1LoopTangent (m59PairInterpolationLoop C t delta gamma hC) z =
      tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        ⟨(t, delta z, gamma z), (0, (c1LoopTangent delta z).2, (c1LoopTangent gamma z).2)⟩ := by
  apply TotalSpace.ext
  · exact m59PairInterpolationLoop_apply C t delta gamma hC z
  · apply heq_of_eq
    have hd : MDifferentiableAt (𝓡 2) (𝓡 3)
        (delta.extension ∘ radialNormalization) z.val :=
      (contMDiffAt_loop_extension (contMDiffOn_radial_extension delta) z).mdifferentiableAt
        one_ne_zero
    have hg : MDifferentiableAt (𝓡 2) (𝓡 3)
        (gamma.extension ∘ radialNormalization) z.val :=
      (contMDiffAt_loop_extension (contMDiffOn_radial_extension gamma) z).mdifferentiableAt
        one_ne_zero
    have hinput : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
        (fun w => (t, delta.extension (radialNormalization w),
          gamma.extension (radialNormalization w))) z.val :=
      mdifferentiableAt_const.prodMk (hd.prodMk hg)
    have heq : (t, delta.extension (radialNormalization z.val),
        gamma.extension (radialNormalization z.val)) = (t, delta z, gamma z) := by
      rw [radialNormalization_of_norm_eq_one z.property, delta.boundary, gamma.boundary]
    have hchain := mfderiv_comp_apply_of_eq z.val ((hC z).mdifferentiableAt one_ne_zero)
      hinput heq (loopCircleTangent z)
    erw [mfderiv_prodMk mdifferentiableAt_const (hd.prodMk hg), mfderiv_prodMk hd hg] at hchain
    simp only [mfderiv_const] at hchain
    change mfderiv (𝓡 2) (𝓡 3)
        (fun w => C (t, delta.extension (radialNormalization w),
          gamma.extension (radialNormalization w))) z.val (loopCircleTangent z) =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C (t, delta z, gamma z)
        (0, mfderiv (𝓡 2) (𝓡 3) (delta.extension ∘ radialNormalization) z.val (loopCircleTangent z),
          mfderiv (𝓡 2) (𝓡 3) (gamma.extension ∘ radialNormalization) z.val (loopCircleTangent z))
      at hchain
    erw [mfderiv_radial_extension delta z, mfderiv_radial_extension gamma z] at hchain
    exact hchain

theorem continuous_m59PairInterpolation_input :
    Continuous (fun v : ℝ × (TangentBundle (𝓡 3) M × TangentBundle (𝓡 3) M) =>
      (⟨(v.1, v.2.1.proj, v.2.2.proj), (0, v.2.1.2, v.2.2.2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (ℝ × (M × M)))) := by
  have ht : Continuous (fun v : ℝ × (TangentBundle (𝓡 3) M × TangentBundle (𝓡 3) M) =>
      (⟨v.1, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_fst
  have hpair : Continuous (fun v : ℝ × (TangentBundle (𝓡 3) M × TangentBundle (𝓡 3) M) =>
      (⟨(v.2.1.proj, v.2.2.proj), (v.2.1.2, v.2.2.2)⟩ :
        TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓡 3) (I' := 𝓡 3)
      (M := M) (M' := M) (n := 0)).continuous.comp continuous_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
    (I' := (𝓡 3).prod (𝓡 3)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
      (ht.prodMk hpair)

theorem continuous_m59PairInterpolationLoop {X : Type v} [TopologicalSpace X]
    (C : ℝ × (M × M) → M) (t : X → ℝ)
    (delta gamma : X → C1FreeLoopSpace (M := M))
    (hC : ∀ x (z : LoopCircle),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t x, delta x z, gamma x z))
    (ht : Continuous t) (hd : Continuous delta) (hg : Continuous gamma) :
    Continuous (fun x => m59PairInterpolationLoop C (t x) (delta x) (gamma x) (hC x)) := by
  have hdv : Continuous (fun v : X × LoopCircle => delta v.1 v.2) :=
    continuous_loop_eval.comp (hd.prodMap continuous_id)
  have hgv : Continuous (fun v : X × LoopCircle => gamma v.1 v.2) :=
    continuous_loop_eval.comp (hg.prodMap continuous_id)
  have hinput : Continuous (fun v : X × LoopCircle =>
      (t v.1, delta v.1 v.2, gamma v.1 v.2)) :=
    (ht.comp continuous_fst).prodMk (hdv.prodMk hgv)
  have hvalues : Continuous (fun v : X × LoopCircle =>
      C (t v.1, delta v.1 v.2, gamma v.1 v.2)) :=
    continuous_iff_continuousAt.mpr fun v => (hC v.1 v.2).continuousAt.comp
      (f := fun w : X × LoopCircle => (t w.1, delta w.1 w.2, gamma w.1 w.2))
      hinput.continuousAt
  have hdt : Continuous (fun v : X × LoopCircle => c1LoopTangent (delta v.1) v.2) :=
    continuous_loop_tangent_eval.comp (hd.prodMap continuous_id)
  have hgt : Continuous (fun v : X × LoopCircle => c1LoopTangent (gamma v.1) v.2) :=
    continuous_loop_tangent_eval.comp (hg.prodMap continuous_id)
  have htinput : Continuous (fun v : X × LoopCircle =>
      (⟨(t v.1, delta v.1 v.2, gamma v.1 v.2),
        (0, (c1LoopTangent (delta v.1) v.2).2, (c1LoopTangent (gamma v.1) v.2).2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (ℝ × (M × M)))) :=
    continuous_m59PairInterpolation_input.comp
      ((ht.comp continuous_fst).prodMk (hdt.prodMk hgt))
  have htangents : Continuous (fun v : X × LoopCircle =>
      tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        ⟨(t v.1, delta v.1 v.2, gamma v.1 v.2),
          (0, (c1LoopTangent (delta v.1) v.2).2, (c1LoopTangent (gamma v.1) v.2).2)⟩) :=
    continuous_iff_continuousAt.mpr fun v =>
      (continuousAt_tangentMap_of_contMDiffAt (hC v.1 v.2)).comp htinput.continuousAt
  apply (continuous_iff_values_tangents _).mpr
  constructor
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun v : X × LoopCircle =>
      m59PairInterpolationLoop C (t v.1) (delta v.1) (gamma v.1) (hC v.1) v.2)
    simpa only [m59PairInterpolationLoop_apply] using hvalues
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun v : X × LoopCircle =>
      c1LoopTangent (m59PairInterpolationLoop C (t v.1) (delta v.1) (gamma v.1) (hC v.1)) v.2)
    simpa only [m59PairInterpolationLoop_tangent] using htangents

end PoincareConjecture
