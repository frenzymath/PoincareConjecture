import PoincareConjecture.Proofs.M03.CurvatureFirstBianchi
import PoincareConjecture.Proofs.M03.CurvatureExtension









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureTensor_pair_exchange
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z =
      D.curvatureTensor x w z u v := by
  obtain ⟨U₁, hU₁, hu⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  obtain ⟨U₂, hU₂, hv⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨U₃, hU₃, hw⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨U₄, hU₄, hz⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) z
  obtain ⟨U, hU, hUopen, hx⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hU₁ (Filter.inter_mem hU₂ (Filter.inter_mem hU₃ hU₄)))
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  let S := fun A : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  have hX : S X := hu.mono fun _ hy => (hU hy).1
  have hY : S Y := hv.mono fun _ hy => (hU hy).2.1
  have hZ : S Z := hw.mono fun _ hy => (hU hy).2.2.1
  have hW : S W := hz.mono fun _ hy => (hU hy).2.2.2
  let P := fun (A B C E : (y : M) → TangentSpace (𝓡 n) y) =>
    g.inner x (D.curvatureOnFields A B C x) (E x)
  have hswap₁ (A B C E : (y : M) → TangentSpace (𝓡 n) y) :
      P A B C E = -P B A C E := by
    simpa only [P, map_neg, neg_apply] using congrArg (fun v => g.inner x v (E x))
      (curvatureOnFields_swap D A B C x)
  have hswap₂ (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) :
      P A B C E = -P A B E C := by
    have h := curvatureOnFields_pair_skew D hUopen A B C E hA hB hC hE hx
    rw [g.symm x (C x) (D.curvatureOnFields A B E x)] at h
    exact h
  have hbianchi (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      P A B C E + P B C A E + P C A B E = 0 := by
    have h := congrArg (fun v => g.inner x v (E x))
      (curvatureOnFields_first_bianchi D hUopen A B C hA hB hC hx)
    simpa only [P, map_add, add_apply, map_zero, zero_apply] using h
  have hpair (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) :
      P A B C E = P C E A B := by
    have h₁ := hbianchi A B C E hA hB hC
    have h₂ := hbianchi B C E A hB hC hE
    have h₃ := hbianchi C A E B hC hA hE
    have h₄ := hbianchi E B A C hE hB hA
    rw [hswap₂ B C A E hB hC hA hE, hswap₂ C A B E hC hA hB hE] at h₁
    rw [hswap₂ C E B A hC hE hB hA, hswap₂ E B C A hE hB hC hA] at h₂
    rw [hswap₂ A E C B hA hE hC hB, hswap₁ E C A B] at h₃
    rw [hswap₁ B A E C, hswap₂ A B E C hA hB hE hC, neg_neg] at h₄
    linarith only [h₁, h₂, h₃, h₄]
  have h := hpair X Y W Z hX hY hW hZ
  rw [hswap₁ W Z X Y, hswap₂ Z W X Y hZ hW hX hY, neg_neg] at h
  delta LeviCivitaData.curvatureTensor LeviCivitaData.curvature
  simpa only [P, X, Y, Z, W, FiberBundle.extend_apply_self] using h

end PoincareConjecture.Proofs.M03
