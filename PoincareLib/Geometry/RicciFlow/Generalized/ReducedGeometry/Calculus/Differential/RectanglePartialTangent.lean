import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Differential.WithinVelocitySmooth

/-!
# Partial tangent fields on a closed-by-open rectangle

The field-regularity step of Morgan-Tian Lemma 6.4, pp. 107-108.
The open factor has its actual unrestricted partial derivative, even at
a boundary point of the other factor. The within chain rule suffices.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

variable {𝕜 E F E' H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E' H}
  [TopologicalSpace M] [ChartedSpace H M]
  {S : Set E} {U : Set F} {α : E × F → M} {m k : ℕ∞ω}

/-- The first-factor within derivative agrees with the corresponding
rectangle partial, including closed endpoints, in the reparametrization
step of Morgan-Tian equation (6.2), p. 106. -/
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

-- Rewriting the product self-model also transports its charted-space instance.
set_option backward.isDefEq.respectTransparency false in
/-- The first within partial tangent is smooth on a rectangle with unique
derivatives in both factors, including closed time endpoints, as used
in Morgan-Tian Lemma 6.4, pp. 107-108. -/
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

/-- The actual second-factor derivative equals the corresponding within
partial derivative, including boundary points of the first factor, as
used in Lemma 6.4, pp. 107-108. -/
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

-- Rewriting the product self-model also transports its charted-space instance.
set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of the actual second-factor tangent field on a rectangle,
with unique derivatives in the first factor and an open second factor;
the regularity step of Lemma 6.4, pp. 107-108. -/
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
