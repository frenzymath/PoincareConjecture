import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

theorem smooth_left_inverse_mfderiv_bijective {f : M → N} {g : N → M} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hg : ContMDiffOn (𝓡 n) (𝓡 n) ∞ g (f '' U))
    (hinv : Set.LeftInvOn g f U) {x : M} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := by
  have hfx := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcomp : (mfderivWithin (𝓡 n) (𝓡 n) g (f '' U) (f x)).comp
      (mfderiv (𝓡 n) (𝓡 n) f x) = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x) := by
    rw [← mfderivWithin_eq_mfderiv (hU.uniqueMDiffOn x hx) hfx]
    rw [← mfderivWithin_comp x
      ((hg (f x) (Set.mem_image_of_mem f hx)).mdifferentiableWithinAt (by simp))
      (hfx.mdifferentiableWithinAt) (fun y hy => Set.mem_image_of_mem f hy)
      (hU.uniqueMDiffOn x hx)]
    exact (mfderivWithin_congr (f₁ := g ∘ f) (f := id)
      (fun y hy => hinv hy) (hinv hx)).trans (mfderivWithin_id (hU.uniqueMDiffOn x hx))
  have hleft : Function.LeftInverse
      (mfderivWithin (𝓡 n) (𝓡 n) g (f '' U) (f x)) (mfderiv (𝓡 n) (𝓡 n) f x) := by
    intro v
    exact congrArg (fun L => L v) hcomp
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
      Module.finrank ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    rfl
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  exact ⟨hleft.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hleft.injective⟩

theorem smooth_left_inverse_image_open {f : M → N} {g : N → M} {U V : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hg : ContMDiffOn (𝓡 n) (𝓡 n) ∞ g (f '' U))
    (hinv : Set.LeftInvOn g f U) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsOpen (f '' V) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (hf.contMDiffAt (hU.mem_nhds (hVU hx)))
    (smooth_left_inverse_mfderiv_bijective hU hf hg hinv (hVU hx))]
  exact image_mem_map (hV.mem_nhds hx)

theorem smooth_left_inverse_openEmbedding {f : M → N} {g : N → M} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hg : ContMDiffOn (𝓡 n) (𝓡 n) ∞ g (f '' U))
    (hinv : Set.LeftInvOn g f U) :
    Topology.IsOpenEmbedding (fun x : U => f x.val) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    hf.continuousOn.domRestrict
  · intro x y hxy
    exact Subtype.ext (hinv.injOn x.property y.property hxy)
  · intro V hV
    change IsOpen ((fun x : U => f x.val) '' V)
    have hval := hU.isOpenEmbedding_subtypeVal.isOpenMap V hV
    have hsub : Subtype.val '' V ⊆ U := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    simpa only [Set.image_image] using
      smooth_left_inverse_image_open hU hf hg hinv hval hsub

end PoincareConjecture.M38
