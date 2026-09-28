import PoincareConjecture.Proofs.M14.Mathlib.WithinVelocitySmooth









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

variable {𝕜 E F E' H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E' H}
  [TopologicalSpace M] [ChartedSpace H M]
  {S : Set E} {U : Set F} {α : E × F → M} {m k : ℕ∞ω}




theorem mfderivWithin_fst_eq_mfderivWithin_prod
    {x : E} {y : F} (hS : UniqueDiffWithinAt 𝕜 S x) (hy : y ∈ U)
    (hα : MDifferentiableWithinAt ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I
      α (S ×ˢ U) (x, y)) (v : E) :
    mfderivWithin (𝓘(𝕜, E)) I (fun r => α (r, y)) S x v =
      mfderivWithin ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I α (S ×ˢ U) (x, y) (v, 0) := by
  have hi : MDifferentiableAt (𝓘(𝕜, E)) ((𝓘(𝕜, E)).prod (𝓘(𝕜, F)))
      (fun r : E => (r, y)) x := mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hchain := mfderivWithin_comp (I := 𝓘(𝕜, E))
    (I' := (𝓘(𝕜, E)).prod (𝓘(𝕜, F))) (I'' := I)
    (f := fun r : E => (r, y)) (g := α) x hα
    hi.mdifferentiableWithinAt
    (fun _ hr => ⟨hr, hy⟩) hS.uniqueMDiffWithinAt
  rw [mfderivWithin_eq_mfderiv hS.uniqueMDiffWithinAt hi, mfderiv_prod_left] at hchain
  exact congrArg (fun L => L v) hchain


set_option backward.isDefEq.respectTransparency false in



theorem ContMDiffOn.contMDiffOn_partialTangentWithin_fst_prod
    [IsManifold I 1 M]
    (hα : ContMDiffOn ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I m α (S ×ˢ U))
    (hS : UniqueDiffOn 𝕜 S) (hU : UniqueDiffOn 𝕜 U) (v : E) (hkm : k + 1 ≤ m) :
    ContMDiffOn ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I.tangent k
      (fun z => Bundle.TotalSpace.mk' E' (α z)
        (mfderivWithin (𝓘(𝕜, E)) I (fun r => α (r, z.2)) S z.1 v)) (S ×ˢ U) := by
  have hα' : ContMDiffOn (𝓘(𝕜, E × F)) I m α (S ×ˢ U) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hα
  have h := hα'.contMDiffOn_mfderivWithin_const_apply (hS.prod hU) (v, 0) hkm
  have hpartial : ContMDiffOn (𝓘(𝕜, E × F)) I.tangent k
      (fun z => Bundle.TotalSpace.mk' E' (α z)
        (mfderivWithin (𝓘(𝕜, E)) I (fun r => α (r, z.2)) S z.1 v)) (S ×ˢ U) := by
    apply h.congr
    intro z hz
    have hm : (1 : ℕ∞ω) ≤ m := le_trans le_add_self hkm
    have heq := mfderivWithin_fst_eq_mfderivWithin_prod (hS z.1 hz.1) hz.2
      ((hα z hz).mdifferentiableWithinAt (ne_of_gt (zero_lt_one.trans_le hm))) v
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at heq
    exact congrArg (fun w : TangentSpace I (α z) => Bundle.TotalSpace.mk' E' (α z) w) heq
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hpartial
  exact hpartial




theorem mfderiv_snd_eq_mfderivWithin_prod (hU : IsOpen U)
    {x : E} {y : F} (hx : x ∈ S) (hy : y ∈ U)
    (hα : MDifferentiableWithinAt ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I
      α (S ×ˢ U) (x, y)) (v : F) :
    mfderiv (𝓘(𝕜, F)) I (fun r => α (x, r)) y v =
      mfderivWithin ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I α (S ×ˢ U) (x, y) (0, v) := by
  have hchain := mfderivWithin_comp (I := 𝓘(𝕜, F))
    (I' := (𝓘(𝕜, E)).prod (𝓘(𝕜, F))) (I'' := I)
    (f := fun r : F => (x, r)) (g := α) y hα
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id).mdifferentiableWithinAt
    (fun _ hr => ⟨hx, hr⟩) (hU.uniqueMDiffOn y hy)
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hy),
    mfderivWithin_of_mem_nhds (hU.mem_nhds hy), mfderiv_prod_right] at hchain
  exact congrArg (fun L => L v) hchain


set_option backward.isDefEq.respectTransparency false in



theorem ContMDiffOn.contMDiffOn_partialTangent_snd_prod
    [IsManifold I 1 M]
    (hα : ContMDiffOn ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I m α (S ×ˢ U))
    (hS : UniqueDiffOn 𝕜 S) (hU : IsOpen U) (v : F) (hkm : k + 1 ≤ m) :
    ContMDiffOn ((𝓘(𝕜, E)).prod (𝓘(𝕜, F))) I.tangent k
      (fun z => Bundle.TotalSpace.mk' E' (α z)
        (mfderiv (𝓘(𝕜, F)) I (fun r => α (z.1, r)) z.2 v)) (S ×ˢ U) := by
  have hα' : ContMDiffOn (𝓘(𝕜, E × F)) I m α (S ×ˢ U) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hα
  have h := hα'.contMDiffOn_mfderivWithin_const_apply
    (hS.prod hU.uniqueDiffOn) (0, v) hkm
  have hpartial : ContMDiffOn (𝓘(𝕜, E × F)) I.tangent k
      (fun z => Bundle.TotalSpace.mk' E' (α z)
        (mfderiv (𝓘(𝕜, F)) I (fun r => α (z.1, r)) z.2 v)) (S ×ˢ U) := by
    apply h.congr
    intro z hz
    have hm : (1 : ℕ∞ω) ≤ m := le_trans (le_add_self) hkm
    have heq := mfderiv_snd_eq_mfderivWithin_prod hU hz.1 hz.2
      ((hα z hz).mdifferentiableWithinAt (ne_of_gt (zero_lt_one.trans_le hm))) v
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at heq
    exact congrArg (fun w : TangentSpace I (α z) => Bundle.TotalSpace.mk' E' (α z) w) heq
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hpartial
  exact hpartial
