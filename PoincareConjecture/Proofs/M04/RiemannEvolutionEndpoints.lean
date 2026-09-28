import PoincareConjecture.Proofs.M04.FlowRiemannRegularity
import PoincareConjecture.Proofs.M04.RicciEvolutionEndpoints
import PoincareConjecture.Proofs.M04.RiemannEvolutionInterior








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
private theorem continuousOn_metric_pairing (F : RicciFlow n M J)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦ (F.metric t).inner x a b) J := by
  let E := EuclideanSpace ℝ (Fin n)
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hfamily := F.smooth.comp hslice.contMDiffOn
    (show MapsTo (fun t : ℝ ↦ (t, x)) J (J ×ˢ univ) from
      fun _ ht ↦ ⟨ht, mem_univ x⟩)
  have hm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t ↦ (F.metric t).inner x a b) J := by
    intro t ht
    have he : ContMDiffWithinAt 𝓘(ℝ, ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun s ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x ((F.metric s).inner x a b)) J t :=
      (hfamily t ht).clm_bundle_apply₂
        (contMDiffWithinAt_const (c := Bundle.TotalSpace.mk' E x a))
        (contMDiffWithinAt_const (c := Bundle.TotalSpace.mk' E x b))
    simp only [Bundle.contMDiffWithinAt_totalSpace] at he
    exact he.2
  exact hm.contDiffOn.continuousOn

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
private theorem continuousOn_curvature_fiber (F : RicciFlow n M J)
    (x : M) (u v z : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦ (F.connection t).curvature x u v z) J := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) x
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun t ↦ (F.metric t).inner x
  let K : ℝ → E := fun t ↦ (F.connection t).curvature x u v z
  let P : ℝ → E →L[ℝ] ℝ := fun t ↦ B t (K t)
  have hB : ContinuousOn B J := by
    have h := (continuousOn_clm_apply (𝕜 := ℝ) (f := B) (s := J)).mpr (by
      intro a
      have ha := (continuousOn_clm_apply (𝕜 := ℝ) (f := fun t ↦ B t a) (s := J)).mpr
        (fun b ↦ continuousOn_metric_pairing F x a b)
      simpa only using! ha)
    simpa only using! h
  have hP : ContinuousOn P J := by
    apply continuousOn_clm_apply.mpr
    intro a
    exact (contDiffOn_curvatureTensor_timeSlice F x u v a z).continuousOn
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : ℝ → E →L[ℝ] E := fun t ↦ Q.toContinuousLinearMap.comp (B t)
  have hA : ContinuousOn A J := continuousOn_const.clm_comp hB
  have hInv (t : ℝ) : (A t).IsInvertible := by
    have hz (a : E) (ha : A t a = 0) : a = 0 := by
      have hBa : B t a = 0 := Q.injective (by simpa [A] using ha)
      have hi : (F.metric t).inner x a a = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L a) hBa
      by_contra hne
      exact (ne_of_gt ((F.metric t).pos x a hne)) hi
    have hinj : Function.Injective (A t) := by
      intro a b hab
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, hab, sub_self]
    have hsurj : Function.Surjective (A t) := LinearMap.injective_iff_surjective.mp hinj
    exact ⟨(LinearEquiv.ofBijective (A t).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext a; rfl⟩
  have hAi : ContinuousOn (fun t ↦ (A t).inverse) J := by
    intro t ht
    have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A t) :=
      (hInv t).contDiffAt_map_inverse
    exact hi.continuousAt.comp_continuousWithinAt (hA t ht)
  have hrec : ContinuousOn (fun t ↦ (A t).inverse (Q (P t))) J :=
    hAi.clm_apply (Q.continuous.comp_continuousOn hP)
  apply hrec.congr
  intro t ht
  symm
  apply (hInv t).inverse_apply_eq.mpr
  rfl

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
private theorem continuousOn_secondRicci_pairing (F : RicciFlow n M J)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦ (F.connection t).iteratedCovariantTensorDerivative
      (F.connection t).ricciEvaluation 2 x ![a, b, c, d]) J := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let U := e.baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt' x
  let X : Fin 4 → (y : M) → TangentSpace (𝓡 n) y :=
    ![FiberBundle.extend E a, FiberBundle.extend E b,
      FiberBundle.extend E c, FiberBundle.extend E d]
  have hX (i : Fin 4) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (X i)) U := by
    fin_cases i
    · exact contMDiffOn_extend_baseSet a
    · exact contMDiffOn_extend_baseSet b
    · exact contMDiffOn_extend_baseSet c
    · exact contMDiffOn_extend_baseSet d
  have hfamily := contMDiffOn_flow_iteratedCovariantTensorDerivative F
    (fun s ↦ isSmoothCovariantTensor_ricciEvaluation (F.connection s))
    (fun V hV Y hY ↦ contMDiffOn_flow_ricciEvaluation F hV hY) 2 e.open_baseSet hX
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hs := hfamily.comp hslice.contMDiffOn
    (show MapsTo (fun t : ℝ ↦ (t, x)) J (J ×ˢ U) from fun _ ht ↦ ⟨ht, hx⟩)
  have ht : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t ↦ (F.connection t).iteratedCovariantTensorDerivative
        (F.connection t).ricciEvaluation 2 x ![a, b, c, d]) J := by
    apply hs.congr
    intro t ht
    apply congrArg ((F.connection t).iteratedCovariantTensorDerivative
      (F.connection t).ricciEvaluation 2 x)
    funext i
    fin_cases i <;> simp [X, FiberBundle.extend_apply_self]
  exact ht.contDiffOn.continuousOn

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem continuousOn_ricci_curvature_pairing (F : RicciFlow n M J)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦ (F.connection t).ricci x
      ((F.connection t).curvature x u v z) w) J := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) x
  choose T hT using fun t : ℝ ↦ (isSmoothCovariantTensor_ricciEvaluation (F.connection t)).1 x
  let L : ℝ → E →L[ℝ] ℝ := fun t ↦ ((T t).toLinearMap ![0, w] 0).toContinuousLinearMap
  have hLval (t : ℝ) (a : E) : L t a = (F.connection t).ricci x a w := by
    have hu : Function.update ![0, w] 0 a = ![a, w] := by
      funext i
      fin_cases i <;> simp [Function.update]
    change T t (Function.update ![0, w] 0 a) = (F.connection t).ricci x a w
    rw [hu]
    exact (hT t ![a, w]).symm
  have hL : ContinuousOn L J := by
    apply continuousOn_clm_apply.mpr
    intro a
    apply (contDiffOn_ricci_timeSlice F x a w).continuousOn.congr
    intro t ht
    exact hLval t a
  apply (hL.clm_apply (continuousOn_curvature_fiber F x u v z)).congr
  intro t ht
  exact (hLval t _).symm

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_curvatureTensor_evolution (F : RicciFlow n M J)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦
      (F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) J := by
  have hK := continuousOn_ricci_curvature_pairing F x u v w z
  have hH := continuousOn_secondRicci_pairing F x
  have hs := ((((((continuousOn_const (c := (-2 : ℝ))).mul hK).sub (hH u v z w)).sub
    (hH u z v w)).add (hH u w v z)).add (hH v u z w)).add (hH v z u w)
  apply (hs.sub (hH v w u z)).congr
  intro t ht
  exact (curvature_firstVariation_eq_laplacian_add_reaction (F.connection t) x u v w z).symm

theorem curvatureTensor_timeDerivative_extend (F : RicciFlow n M J)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) (q : ℝ → ℝ)
    (hq : ContinuousOn q J)
    (hi : ∀ t ∈ interior J,
      HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z) (q t) t) :
    ∀ t ∈ J, HasDerivWithinAt
      (fun s ↦ (F.connection s).curvatureTensor x u v w z) (q t) J t := by
  let f := fun t ↦ (F.connection t).curvatureTensor x u v w z
  have hf : ContDiffOn ℝ ∞ f J := contDiffOn_curvatureTensor_timeSlice F x u v w z
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty := hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconv hne
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hinside : EqOn (derivWithin f J) q (interior J) := by
    intro t ht
    exact (hi t ht).hasDerivWithinAt.derivWithin (hJ t (interior_subset ht))
  have heq : EqOn (derivWithin f J) q J := hinside.of_subset_closure
    (hf.continuousOn_derivWithin hJ (by simp)) hq interior_subset hdense
  intro t ht
  exact ((hf t ht).differentiableWithinAt (by simp)).hasDerivWithinAt.congr_deriv (heq ht)

end PoincareConjecture.M04

