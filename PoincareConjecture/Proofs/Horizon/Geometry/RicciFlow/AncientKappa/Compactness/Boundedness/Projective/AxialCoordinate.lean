import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Collar








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture



theorem cylinderCover_axialCoordinate_mfderiv
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {f : RoundCylinderSpace → M} {s : ℝ}
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-s) s))
    {a : M → ℝ}
    (ha : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-s) s)))
    (hvalue : ∀ z ∈ univ ×ˢ Ioo (-s) s, a (f z) = z.2)
    {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-s) s)
    (v : RoundCylinderTangent z) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) a (f z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z v) = v.2 := by
  have hsopen : IsOpen (univ ×ˢ Ioo (-s) s : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  have haat : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f z) := by
    apply ha.contMDiffAt
    rw [← hf.isLocalHomeomorphOn.map_nhds_eq hz]
    exact Filter.image_mem_map (hsopen.mem_nhds hz)
  have heq : a ∘ f =ᶠ[𝓝 z] Prod.snd :=
    Filter.eventuallyEq_of_mem (hsopen.mem_nhds hz) hvalue
  rw [← mfderiv_comp_apply z (haat.mdifferentiableAt (by simp))
    ((hf ⟨z, hz⟩).mdifferentiableAt (by simp)), heq.mfderiv_eq, mfderiv_snd]
  rfl




theorem exists_projectiveCylinderSlab_axialCoordinate
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (f : RoundCylinderSpace → M) {s : ℝ}
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-s) s))
    (hfiber : ∀ z ∈ univ ×ˢ Ioo (-s) s, ∀ w ∈ univ ×ˢ Ioo (-s) s,
      f z = f w ↔ w = z ∨ w = (-z.1, z.2)) :
    ∃ a : M → ℝ,
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-s) s)) ∧
      (∀ z ∈ univ ×ˢ Ioo (-s) s, a (f z) = z.2) ∧
      (∀ z ∈ univ ×ˢ Ioo (-s) s, ∀ v : RoundCylinderTangent z,
        mfderiv (𝓡 3) 𝓘(ℝ, ℝ) a (f z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z v) = v.2) ∧
      ∀ x ∈ f '' (univ ×ˢ Ioo (-s) s), mfderiv (𝓡 3) 𝓘(ℝ, ℝ) a x ≠ 0 := by
  classical
  obtain ⟨hopen, e, he⟩ := exists_projectiveCylinderSlab_homeomorph f
    hf.isLocalHomeomorphOn hfiber
  let U := f '' (univ ×ˢ Ioo (-s) s)
  let a : M → ℝ := fun x => if hx : x ∈ U then (e.symm ⟨x, hx⟩).2.val else 0
  have hvalue (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-s) s) :
      a (f z) = z.2 := by
    have hx : f z ∈ U := ⟨z, hz, rfl⟩
    have heq : e (Quotient.mk realProjectiveTwoSetoid z.1, ⟨z.2, hz.2⟩) =
        (⟨f z, hx⟩ : U) := Subtype.ext (he z.1 ⟨z.2, hz.2⟩)
    dsimp only [a]
    rw [dif_pos hx, ← heq, e.symm_apply_apply]
  have hsopen : IsOpen (univ ×ˢ Ioo (-s) s : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  have ha (x : M) (hx : x ∈ U) : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ a x := by
    obtain ⟨z, hz, rfl⟩ := hx
    let hloc := hf ⟨z, hz⟩
    have hinv : hloc.localInverse (f z) = z :=
      hloc.localInverse_left_inv hloc.localInverse_mem_target
    have hmem : ∀ᶠ y in 𝓝 (f z), hloc.localInverse y ∈ univ ×ˢ Ioo (-s) s := by
      apply hloc.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds
      rw [hinv]
      exact hsopen.mem_nhds hz
    have heq : a =ᶠ[𝓝 (f z)] (fun y => (hloc.localInverse y).2) := by
      filter_upwards [hmem,
        hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source] with y hy hyinv
      exact (congrArg a (hloc.localInverse_right_inv hyinv)).symm.trans
        (hvalue (hloc.localInverse y) hy)
    exact (contMDiffAt_snd.comp (f z) hloc.localInverse_contMDiffAt).congr_of_eventuallyEq heq
  have hderiv (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-s) s)
      (v : RoundCylinderTangent z) :
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) a (f z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z v) = v.2 := by
    have heq : a ∘ f =ᶠ[𝓝 z] Prod.snd :=
      Filter.eventuallyEq_of_mem (hsopen.mem_nhds hz) hvalue
    rw [← mfderiv_comp_apply z
      ((ha (f z) ⟨z, hz, rfl⟩).mdifferentiableAt (by simp))
      ((hf ⟨z, hz⟩).mdifferentiableAt (by simp)), heq.mfderiv_eq]
    rw [mfderiv_snd]
    rfl
  refine ⟨a, (fun x hx => (ha x hx).contMDiffWithinAt), hvalue, hderiv, ?_⟩
  rintro x ⟨z, hz, rfl⟩ hzero
  have h := hderiv z hz (0, 1)
  rw [hzero, zero_apply] at h
  exact (zero_ne_one : (0 : ℝ) ≠ 1) h

end PoincareConjecture
