import PoincareConjecture.Proofs.M09.ManifoldLocalInverse
import PoincareConjecture.Proofs.M09.TriangularBijective
import PoincareConjecture.Proofs.M09.FamilySlices

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_spacetime_bijective_iff (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) (ht : 0 < τ) (hm : τ < τmax) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    Function.Bijective (mfderiv ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ)))
      ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      (fun z : TangentSpace (𝓡 n) p × ℝ ↦ (A.gamma z.1 z.2, z.2)) (Z, τ)) ↔
      Function.Bijective (A.sliceDifferential Z τ) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hgs := A.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show (Z, τ) ∈ Set.univ ×ˢ Set.Ioo 0 τmax from ⟨Set.mem_univ _, ht, hm⟩))
  have hg := hgs.mdifferentiableAt (by simp)
  rw [mfderiv_prodMk hg mdifferentiableAt_snd, mfderiv_snd]
  apply triangular_bijective_iff _ (A.sliceDifferential Z τ)
  · intro z
    rfl
  · intro W
    change mfderiv ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) (𝓡 n)
      (fun z ↦ A.gamma z.1 z.2) (Z, τ) (W, 0) = A.sliceDifferential Z τ W
    rw [mfderiv_prod_eq_add_apply hg]
    simp only [map_zero, add_zero, LExponentialFamily.sliceDifferential]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_exists_local_inverse (A : LExponentialFamily F T τmax p)
    (z : TangentSpace (𝓡 n) p × ℝ) (ht : 0 < z.2) (hm : z.2 < τmax)
    (hbij : Function.Bijective (A.sliceDifferential z.1 z.2)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∃ e : OpenPartialHomeomorph (TangentSpace (𝓡 n) p × ℝ) (M × ℝ),
      z ∈ e.source ∧ e.source ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      Set.EqOn e (fun w ↦ (A.gamma w.1 w.2, w.2)) e.source ∧
      ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, TangentSpace (𝓡 n) p)).prod (𝓘(ℝ, ℝ))) ∞ e.symm e.target ∧
      ∀ w ∈ e.source, Function.Bijective (A.sliceDifferential w.1 w.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (M × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) M ℝ ℝ
  letI : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) M ℝ
  let Φ : TangentSpace (𝓡 n) p × ℝ → M × ℝ := fun w ↦ (A.gamma w.1 w.2, w.2)
  have hf : ContMDiffOn (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) ∞ Φ (Set.univ ×ˢ Set.Ioo 0 τmax) := by
    convert! A.gamma_smooth.prodMk contMDiffOn_snd using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hfull : Function.Bijective (mfderiv (𝓘(ℝ, TangentSpace (𝓡 n) p × ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)) Φ z) := by
    convert! (lExponentialFamily_spacetime_bijective_iff A z.1 z.2 ht hm).mpr hbij using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    congr 2 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  obtain ⟨e, hze, hsub, he, hinv, hderiv⟩ := exists_manifold_local_inverse Φ
    (Set.univ ×ˢ Set.Ioo 0 τmax) (isOpen_univ.prod isOpen_Ioo) hf z
    ⟨Set.mem_univ _, ht, hm⟩ hfull
  refine ⟨e, hze, hsub, he, ?_, ?_⟩
  · convert! hinv using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  · intro w hw
    apply (lExponentialFamily_spacetime_bijective_iff A w.1 w.2 (hsub hw).2.1 (hsub hw).2.2).mp
    convert! hderiv w hw using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    congr 2 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]

end PoincareConjecture.Proofs.M09
