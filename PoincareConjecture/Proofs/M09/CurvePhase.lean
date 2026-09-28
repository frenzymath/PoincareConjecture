import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Separation.Hausdorff








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def curvePhase (γ : ℝ → M) (s : ℝ) : TangentBundle (𝓡 n) M :=
  ⟨γ s, curveVelocity γ s⟩

set_option backward.isDefEq.respectTransparency false in
theorem curvePhase_contMDiffOn (γ : ℝ → M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ I) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞ (curvePhase (n := n) γ) I := by
  have hmodel : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ∞
      (fun q : ℝ × ℝ ↦ (⟨q.1, q.2⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(ℝ, ℝ)) (n := ∞)) using 1
    rw [chartedSpaceSelf_prod]
    rfl
  have ht : ContMDiff (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ∞
      (fun s : ℝ ↦ (⟨s, 1⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) :=
    hmodel.comp (contMDiff_id.prodMk contMDiff_const)
  have h := (hγ.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hI.uniqueMDiffOn).comp
    ht.contMDiffOn (fun s hs ↦ hs)
  apply h.congr
  intro s hs
  change Bundle.TotalSpace.mk' V (γ s) ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s) 1) =
    Bundle.TotalSpace.mk' V (γ s) ((mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ I s) 1)
  rw [mfderivWithin_of_isOpen hI hs]

theorem tangentBundle_t2Space [T2Space M] : T2Space (TangentBundle (𝓡 n) M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hxy
  by_cases hbase : x.proj = y.proj
  · let e := trivializationAt V (TangentSpace (𝓡 n) : M → Type _) x.proj
    have hx : x ∈ e.source := e.mem_source.mpr
      (FiberBundle.mem_baseSet_trivializationAt' x.proj)
    have hy : y ∈ e.source := by
      apply e.mem_source.mpr
      rw [← hbase]
      exact FiberBundle.mem_baseSet_trivializationAt' x.proj
    have hne : e x ≠ e y := fun h ↦ hxy (e.toOpenPartialHomeomorph.injOn hx hy h)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hne) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj V (TangentSpace (𝓡 n))).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase)
      (FiberBundle.continuous_proj V (TangentSpace (𝓡 n))).continuousAt

theorem curvePhase_eventuallyEq {γ δ : ℝ → M} {s : ℝ} (h : γ =ᶠ[𝓝 s] δ) :
    curvePhase (n := n) γ =ᶠ[𝓝 s] curvePhase (n := n) δ := by
  filter_upwards [eventually_eventuallyEq_nhds.2 h] with t ht
  apply Bundle.TotalSpace.ext ht.self_of_nhds
  exact heq_of_eq (congrArg (fun L : ℝ →L[ℝ] V ↦ L 1)
    (ht.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)))

end PoincareConjecture.Proofs.M09
