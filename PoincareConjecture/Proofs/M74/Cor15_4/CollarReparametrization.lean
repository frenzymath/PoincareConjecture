import PoincareConjecture.Proofs.M74.ServiceMirror










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M74



noncomputable def shiftCollarParam (s : ℝ) : ℝ := (1 + 2 * s) / (2 + s)



noncomputable def unshiftCollarParam (t : ℝ) : ℝ := (2 * t - 1) / (2 - t)



theorem shiftCollarParam_mem {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    shiftCollarParam s ∈ Ioo (-1 : ℝ) 1 := by
  have hden : 0 < 2 + s := by linarith [hs.1]
  exact ⟨(lt_div_iff₀ hden).mpr (by linarith [hs.1]),
    (div_lt_iff₀ hden).mpr (by linarith [hs.2])⟩



theorem unshiftCollarParam_mem {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    unshiftCollarParam s ∈ Ioo (-1 : ℝ) 1 := by
  have hden : 0 < 2 - s := by linarith [hs.2]
  exact ⟨(lt_div_iff₀ hden).mpr (by linarith [hs.1]),
    (div_lt_iff₀ hden).mpr (by linarith [hs.2])⟩



theorem unshift_shiftCollarParam {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    unshiftCollarParam (shiftCollarParam s) = s := by
  have hden : 2 + s ≠ 0 := by linarith [hs.1]
  unfold shiftCollarParam unshiftCollarParam
  field_simp
  ring



theorem shift_unshiftCollarParam {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    shiftCollarParam (unshiftCollarParam s) = s := by
  have hden : 2 - s ≠ 0 := by linarith [hs.2]
  unfold shiftCollarParam unshiftCollarParam
  field_simp
  ring



theorem shiftCollarParam_contDiffOn :
    ContDiffOn ℝ ∞ shiftCollarParam (Ioo (-1 : ℝ) 1) := by
  exact (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn.div
    (contDiff_const.add contDiff_id).contDiffOn (fun s hs => by linarith [hs.1])



theorem unshiftCollarParam_contDiffOn :
    ContDiffOn ℝ ∞ unshiftCollarParam (Ioo (-1 : ℝ) 1) := by
  exact ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffOn.div
    (contDiff_const.sub contDiff_id).contDiffOn (fun s hs => by linarith [hs.2])



noncomputable def shiftCollar (p : RoundCylinderSpace) : RoundCylinderSpace :=
  (p.1, shiftCollarParam p.2)

private theorem shiftCollar_mem {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : shiftCollar p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 :=
  ⟨mem_univ _, shiftCollarParam_mem hp.2⟩



theorem shiftCollar_contMDiffOn :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ shiftCollar
      (univ ×ˢ Ioo (-1) 1) :=
  contMDiff_fst.contMDiffOn.prodMk
    (shiftCollarParam_contDiffOn.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))



theorem shiftCollar_mfderiv_injective {p : RoundCylinderSpace}
    (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
    Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      shiftCollar p) := by
  let G : RoundCylinderSpace → RoundCylinderSpace := fun q => (q.1, unshiftCollarParam q.2)
  have hG : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ G
      (univ ×ˢ Ioo (-1) 1) :=
    contMDiff_fst.contMDiffOn.prodMk
      (unshiftCollarParam_contDiffOn.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hq => hq.2))
  have hopen : IsOpen (univ ×ˢ Ioo (-1 : ℝ) 1 : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  have hevent : G ∘ shiftCollar =ᶠ[𝓝 p] id := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact Prod.ext rfl (unshift_shiftCollarParam hq.2)
  have hd := mfderiv_comp p
    ((hG.contMDiffAt (hopen.mem_nhds (shiftCollar_mem hp))).mdifferentiableAt (by simp))
    ((shiftCollar_contMDiffOn.contMDiffAt (hopen.mem_nhds hp)).mdifferentiableAt (by simp))
  rw [hevent.mfderiv_eq, mfderiv_id] at hd
  intro v w hvw
  have h := congrArg
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) G (shiftCollar p)) hvw
  change ((mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) G (shiftCollar p)).comp
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) shiftCollar p)) v =
    ((mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) G (shiftCollar p)).comp
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) shiftCollar p)) w at h
  rw [← hd] at h
  exact h



theorem isCollarEmbedding_comp_shift {ψ : RoundCylinderSpace → M25.Topology3D.E3}
    (hψ : M25.Topology3D.IsCollarEmbedding ψ) :
    M25.Topology3D.IsCollarEmbedding (ψ ∘ shiftCollar) := by
  refine ⟨hψ.1.comp shiftCollar_contMDiffOn (fun _ hp => shiftCollar_mem hp), ?_, ?_⟩
  · intro p hp q hq hpq
    have heq := hψ.2.1 (shiftCollar_mem hp) (shiftCollar_mem hq) hpq
    have hfirst := congrArg Prod.fst heq
    change p.1 = q.1 at hfirst
    apply Prod.ext hfirst
    have h := congrArg (fun z : RoundCylinderSpace => unshiftCollarParam z.2) heq
    simpa only [shiftCollar, unshift_shiftCollarParam hp.2, unshift_shiftCollarParam hq.2] using h
  · intro p hp
    have hopen : IsOpen (univ ×ˢ Ioo (-1 : ℝ) 1 : Set RoundCylinderSpace) :=
      isOpen_univ.prod isOpen_Ioo
    rw [mfderiv_comp p
      ((hψ.1.contMDiffAt (hopen.mem_nhds (shiftCollar_mem hp))).mdifferentiableAt (by simp))
      ((shiftCollar_contMDiffOn.contMDiffAt (hopen.mem_nhds hp)).mdifferentiableAt (by simp))]
    exact (hψ.2.2 _ (shiftCollar_mem hp)).comp (shiftCollar_mfderiv_injective hp)

end PoincareConjecture.M74
