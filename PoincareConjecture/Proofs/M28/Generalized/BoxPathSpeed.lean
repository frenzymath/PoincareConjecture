import PoincareConjecture.Proofs.M28.Generalized.FlowPathSpeed











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M28

variable (F : GeneralizedRicciFlowData.{u}) {ι : Type v} (b : ι → F.box_index)
    (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval)




theorem boxTransport_speed_eq
    (s : ℝ) (hs : ∀ i, s ∈ (F.box (b i)).interval) (hsF : s ∈ F.interval)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContMDiff 𝓘(ℝ) (𝓡 3) 1 γ)
    (i : ι) (v : ℝ) (hv : γ v ∈ range ((F.box (b i)).forward t (ht i))) :
    (F.metric s).tangentNorm (boxTransport F b t s ht hs hsF (γ v))
        (curveVelocity (boxTransport F b t s ht hs hsF ∘ γ) v) =
      ((F.box (b i)).flow.metric s).tangentNorm
        ((F.box (b i)).inverse t (ht i) (γ v))
        (curveVelocity ((F.box (b i)).inverse t (ht i) ∘ γ) v) := by
  have hopen := ((F.box (b i)).forward_openEmbedding t (ht i)).isOpen_range
  have hinv := ((F.box (b i)).inverse_smooth t (ht i)).contMDiffAt
    (hopen.mem_nhds hv)
  have hmodel := hinv.mdifferentiableAt (by norm_num)
    |>.comp v (hγ.mdifferentiable (by norm_num) v)
  have heq : (boxTransport F b t s ht hs hsF ∘ γ) =ᶠ[𝓝 v]
      ((F.box (b i)).forward s (hs i) ∘ (F.box (b i)).inverse t (ht i) ∘ γ) := by
    filter_upwards [hγ.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hv)]
      with w hw
    obtain ⟨x, hx⟩ := hw
    simp only [Function.comp_apply, ← hx, boxTransport_apply,
      (F.box (b i)).left_inverse t (ht i) x]
  change (F.metric s).tangentNorm ((boxTransport F b t s ht hs hsF ∘ γ) v)
    ((mfderiv 𝓘(ℝ) (𝓡 3) (boxTransport F b t s ht hs hsF ∘ γ) v) 1) = _
  rw [heq.eq_of_nhds, heq.mfderiv_eq]
  exact F.tangentNorm_box_curve (b i) s (hs i)
    ((F.box (b i)).inverse t (ht i) ∘ γ) v hmodel




theorem continuousOn_boxTransport_speed
    (J : Set ℝ) (hJF : J ⊆ F.interval)
    (hJ : ∀ s ∈ J, ∀ i, s ∈ (F.box (b i)).interval)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContMDiff 𝓘(ℝ) (𝓡 3) 1 γ) :
    ContinuousOn (fun z : J × ℝ =>
      (F.metric z.1.val).tangentNorm
        (boxTransport F b t z.1.val ht (hJ _ z.1.property) (hJF z.1.property) (γ z.2))
        (curveVelocity
          (boxTransport F b t z.1.val ht (hJ _ z.1.property) (hJF z.1.property) ∘ γ)
          z.2))
      (univ ×ˢ (γ ⁻¹' range (boxEvaluation F b t ht))) := by
  rintro ⟨s, v⟩ ⟨_, hv⟩
  obtain ⟨⟨i, x⟩, hx⟩ := hv
  have hvbox : γ v ∈ range ((F.box (b i)).forward t (ht i)) := ⟨x, hx⟩
  let V := γ ⁻¹' range ((F.box (b i)).forward t (ht i))
  have hV : IsOpen V :=
    ((F.box (b i)).forward_openEmbedding t (ht i)).isOpen_range.preimage hγ.continuous
  have hmodel : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1
      ((F.box (b i)).inverse t (ht i) ∘ γ) V :=
    (((F.box (b i)).inverse_smooth t (ht i)).of_le (by norm_num)).comp
      hγ.contMDiffOn (fun _ hz => hz)
  have hspeed := ((F.box (b i)).flow.continuousOn_tangentNorm_curveVelocity hV hmodel)
  have hlocal : ContinuousOn (fun z : J × ℝ =>
      ((F.box (b i)).flow.metric z.1.val).tangentNorm
        ((F.box (b i)).inverse t (ht i) (γ z.2))
        (curveVelocity ((F.box (b i)).inverse t (ht i) ∘ γ) z.2)) (univ ×ˢ V) :=
    hspeed.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun z hz => ⟨hJ _ z.1.property i, hz.2⟩)
  have hvV : v ∈ V := hvbox
  have hnbhd : univ ×ˢ V ∈ 𝓝 (s, v) :=
    (isOpen_univ.prod hV).mem_nhds ⟨mem_univ s, hvV⟩
  have hlocalAt := hlocal.continuousAt hnbhd
  apply (hlocalAt.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [hnbhd] with z hz
  exact boxTransport_speed_eq F b t ht z.1.val (hJ _ z.1.property)
    (hJF z.1.property) γ hγ i z.2 hz.2

end PoincareConjecture.M28
