import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients
import PoincareConjecture.Proofs.M04.ScalarEvolutionInterior
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv










set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in

theorem contMDiffOn_scalarCurvature :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2)
      (J ×ˢ Set.univ) := by
  classical
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex F.interval.convex
    (F.interval.convex.nontrivial_iff_nonempty_interior.mp F.nontrivial)
  have hclm {E' G : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
      {L : ℝ × M → E' →L[ℝ] G} {V : Set (ℝ × M)} {p : ℝ × M}
      (hL : ∀ v : E', ContMDiffWithinAt I 𝓘(ℝ, G) ∞ (fun q ↦ L q v) V p) :
      ContMDiffWithinAt I 𝓘(ℝ, E' →L[ℝ] G) ∞ L V p := by
    let d := Module.finrank ℝ E'
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e1 := ContinuousLinearEquiv.ofFinrankEq hd
    let e2 := (e1.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
    have hc : ContMDiffWithinAt I 𝓘(ℝ, Fin d → G) ∞ (fun q ↦ e2 (L q)) V p := by
      apply contMDiffWithinAt_pi_space.mpr
      intro i
      exact hL _
    have h := e2.symm.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p hc
    have heq : (fun q ↦ e2.symm (e2 (L q))) = L := by
      funext q
      exact e2.symm_apply_apply (L q)
    have h' : ContMDiffWithinAt I 𝓘(ℝ, E' →L[ℝ] G) ∞
        (fun q ↦ e2.symm (e2 (L q))) V p := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! h
    rwa [heq] at h'
  intro p0 hp0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric p0.1).toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let t := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p0.2
  let V := J ×ˢ t.baseSet
  have hxT : p0.2 ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p0.2
  have hpV : p0 ∈ V := ⟨hp0.1, hxT⟩
  let S := fun y ↦ t.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ t.baseSet) :
      FiberBundle.extend E (S p0.2 v) y = S y v := by
    change t.symm y (t ⟨p0.2, t.symmL ℝ p0.2 v⟩).2 = t.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hxT,
      t.continuousLinearMapAt_symmL hxT, t.symmL_apply hy]
  have hS (v : E) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (fun y ↦ S y v)) t.baseSet := by
    apply (M04.contMDiffOn_extend_baseSet (S p0.2 v)).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy).symm
  have hSP (v : E) : ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' E p.2 (S p.2 v)) V :=
    (hS v).comp contMDiffOn_snd (fun _ h ↦ h.2)
  let B : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2).bilinearComp (S p.2) (S p.2)
  have hBs (v w : E) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p ↦ B p v w) V := by
    intro p hp
    have hg := (F.smooth p ⟨hp.1, Set.mem_univ p.2⟩).mono
      (show V ⊆ J ×ˢ Set.univ from fun q hq ↦ ⟨hq.1, Set.mem_univ q.2⟩)
    have happ : ContMDiffWithinAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          q.2 (B q v w)) V p := by
      exact hg.clm_bundle_apply₂ (hSP v p hp) (hSP w p hp)
    simp only [Bundle.contMDiffWithinAt_totalSpace] at happ
    exact happ.2
  have hPartial {f : ℝ × M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun p ↦ derivWithin (fun τ ↦ f (τ, p.2)) J p.1) V := by
    intro p hp
    have hmap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : (ℝ × M) × ℝ ↦ (q.2, q.1.2)) :=
      contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)
    have hc : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : (ℝ × M) × ℝ ↦ f (q.2, q.1.2)) (V ×ˢ J) (p, p.1) :=
      (hf p hp).comp (p, p.1) (hmap (p, p.1)).contMDiffWithinAt
        (show Set.MapsTo (fun q : (ℝ × M) × ℝ ↦ (q.2, q.1.2)) (V ×ˢ J) V from
          fun _ hq ↦ ⟨hq.2, hq.1.2⟩)
    have hd := ContMDiffWithinAt.mfderivWithin
      (f := fun (q : ℝ × M) (τ : ℝ) ↦ f (τ, q.2)) (g := Prod.fst)
      hc contMDiffWithinAt_fst hp (fun q hq ↦ hq.1) (m := ∞) (by simp)
      hJ.uniqueMDiffOn
    have ha := hd.clm_apply (contMDiffWithinAt_const (c := (1 : ℝ)))
    simpa only [inTangentCoordinates_model_space, mfderivWithin_eq_fderivWithin,
      derivWithin] using! ha
  choose R hR using fun p : ℝ × M ↦
    (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection p.1)).1 p.2
  have hRC (p : ℝ × M) (a b : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 a b = R p ![a, b] := hR p ![a, b]
  have hu0 {p : ℝ × M} (a b z : TangentSpace (𝓡 n) p.2) :
      Function.update ![a, b] 0 z = ![z, b] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hu1 {p : ℝ × M} (a b z : TangentSpace (𝓡 n) p.2) :
      Function.update ![a, b] 1 z = ![a, z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have ha1 (p : ℝ × M) (a b z : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 (a + b) z =
        (F.connection p.1).ricci p.2 a z + (F.connection p.1).ricci p.2 b z := by
    simp only [hRC]
    simpa only [hu0] using (R p).map_update_add ![a, z] 0 a b
  have ha2 (p : ℝ × M) (a b z : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 z (a + b) =
        (F.connection p.1).ricci p.2 z a + (F.connection p.1).ricci p.2 z b := by
    simp only [hRC]
    simpa only [hu1] using (R p).map_update_add ![z, a] 1 a b
  have hs1 (p : ℝ × M) (c : ℝ) (a b : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 (c • a) b =
        c • (F.connection p.1).ricci p.2 a b := by
    simp only [hRC]
    simpa only [hu0] using (R p).map_update_smul ![a, b] 0 c a
  have hs2 (p : ℝ × M) (c : ℝ) (a b : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 a (c • b) =
        c • (F.connection p.1).ricci p.2 a b := by
    simp only [hRC]
    simpa only [hu1] using (R p).map_update_smul ![a, b] 1 c b
  let C : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ LinearMap.toContinuousLinearMap
          { toFun := fun w ↦ (F.connection p.1).ricci p.2 (S p.2 v) (S p.2 w)
            map_add' := by intro a b; rw [map_add, ha2]
            map_smul' := by intro c a; rw [map_smul, hs2]; rfl }
        map_add' := by
          intro a b
          ext w
          change (F.connection p.1).ricci p.2 (S p.2 (a + b)) (S p.2 w) = _
          rw [map_add, ha1]
          rfl
        map_smul' := by
          intro c a
          ext w
          change (F.connection p.1).ricci p.2 (S p.2 (c • a)) (S p.2 w) = _
          rw [map_smul, hs1]
          rfl }
  have hCs (v w : E) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p ↦ C p v w) V := by
    apply ((hPartial (hBs v w)).mul (contMDiffOn_const (c := (-1 / 2 : ℝ)))).congr
    intro p hp
    have he := (F.equation p.1 hp.1 p.2 (S p.2 v) (S p.2 w)).derivWithin (hJ p.1 hp.1)
    change (F.connection p.1).ricci p.2 (S p.2 v) (S p.2 w) =
      derivWithin (fun τ ↦ (F.metric τ).inner p.2 (S p.2 v) (S p.2 w)) J p.1 * (-1 / 2)
    rw [he]
    ring
  have hB : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B V p0 :=
    hclm fun v ↦ hclm fun w ↦ hBs v w p0 hpV
  have hC : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ C V p0 :=
    hclm fun v ↦ hclm fun w ↦ hCs v w p0 hpV
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (B p)
  let H : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (C p)
  have hA : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞ A V p0 :=
    contMDiffWithinAt_const.clm_comp hB
  have hH : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞ H V p0 :=
    contMDiffWithinAt_const.clm_comp hC
  have hInv {p : ℝ × M} (hp : p.2 ∈ t.baseSet) : (A p).IsInvertible := by
    have hz (v : E) (hv : A p v = 0) : v = 0 := by
      have hBv : B p v = 0 := Q.injective (by simpa [A] using hv)
      have hi : (F.metric p.1).inner p.2 (S p.2 v) (S p.2 v) = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hBv
      have hSv : S p.2 v = 0 := by
        by_contra hne
        exact (ne_of_gt ((F.metric p.1).pos p.2 _ hne)) hi
      have hv' := congrArg (t.continuousLinearMapAt ℝ p.2) hSv
      simpa only [S, t.continuousLinearMapAt_symmL hp, map_zero] using hv'
    have hinj : Function.Injective (A p) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (A p) := (LinearMap.injective_iff_surjective).mp hinj
    exact ⟨(LinearEquiv.ofBijective (A p).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  let L := fun p ↦ (A p).inverse.comp (H p)
  have hL : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞ L V p0 :=
    ((hInv hxT).contDiffAt_map_inverse.contMDiffAt.comp_contMDiffWithinAt p0 hA).clm_comp hH
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let tr := fun p ↦ ∑ i, b.repr (L p (b i)) i
  have htr : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ tr V p0 := by
    apply ContMDiffWithinAt.sum
    intro i _
    exact (b.coord i).toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p0
      (hL.clm_apply contMDiffWithinAt_const)
  have htr_eq (p : ℝ × M) : LinearMap.trace ℝ E (L p).toLinearMap = tr p := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, tr]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have heq {p : ℝ × M} (hp : p.2 ∈ t.baseSet) :
      tr p = (F.connection p.1).scalarCurvature p.2 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric p.1).toRiemannianMetric⟩
    let e := (t.continuousLinearEquivAt ℝ p.2 hp).symm
    let K := e.toLinearEquiv.conj (L p).toLinearMap
    have hrec (v : E) : B p (L p v) = C p v := by
      apply Q.injective
      change A p ((A p).inverse (H p v)) = H p v
      exact (hInv hp).self_apply_inverse _
    have hK (a b : TangentSpace (𝓡 n) p.2) :
        (F.metric p.1).inner p.2 (K a) b = (F.connection p.1).ricci p.2 a b := by
      have h := congrArg (fun f : E →L[ℝ] ℝ ↦ f (e.symm b)) (hrec (e.symm a))
      have hSe (v : E) : S p.2 v = e v :=
        (congrFun (t.symm_continuousLinearEquivAt_eq hp) v).symm
      change (F.metric p.1).inner p.2 (S p.2 (L p (e.symm a))) (S p.2 (e.symm b)) =
        (F.connection p.1).ricci p.2 (S p.2 (e.symm a)) (S p.2 (e.symm b)) at h
      simp only [hSe, e.apply_symm_apply] at h
      exact h
    calc
      tr p = LinearMap.trace ℝ E (L p).toLinearMap := (htr_eq p).symm
      _ = LinearMap.trace ℝ (TangentSpace (𝓡 n) p.2) K :=
        (LinearMap.trace_conj' (L p).toLinearMap e.toLinearEquiv).symm
      _ = ∑ i, inner ℝ ((F.metric p.1).orthonormalBasis p.2 i)
          (K ((F.metric p.1).orthonormalBasis p.2 i)) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ ((F.metric p.1).orthonormalBasis p.2).toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change (F.metric p.1).inner p.2 ((F.metric p.1).orthonormalBasis p.2 i)
          (K ((F.metric p.1).orthonormalBasis p.2 i)) =
            (F.connection p.1).ricci p.2 ((F.metric p.1).orthonormalBasis p.2 i)
              ((F.metric p.1).orthonormalBasis p.2 i)
        rw [(F.metric p.1).symm, hK]
  have hScalar : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) V p0 := by
    apply htr.congr_of_eventuallyEq_of_mem ?_ hpV
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (heq hp.2).symm
  apply hScalar.mono_of_mem_nhdsWithin
  have hO : (Prod.snd ⁻¹' t.baseSet : Set (ℝ × M)) ∈ 𝓝 p0 :=
    continuous_snd.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hxT)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with p hp hpt
  exact ⟨hp.1, hpt⟩


theorem contMDiff_scalarCurvature (t : ℝ) (ht : t ∈ J) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F.connection t).scalarCurvature := by
  have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ t) := contMDiff_const
  have hi : ContMDiff (𝓡 n) (𝓡 n) ∞ (fun x : M ↦ x) := contMDiff_id
  have hslice : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun x : M ↦ (t, x)) := hc.prodMk hi
  exact ContMDiffOn.comp_contMDiff (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ).prod (𝓡 n))
    (I'' := 𝓘(ℝ, ℝ)) (f := fun x : M ↦ (t, x))
    (g := fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2)
    F.contMDiffOn_scalarCurvature hslice
    fun x ↦ ⟨ht, Set.mem_univ x⟩


theorem contDiffOn_scalarCurvature_timeSlice (x : M) :
    ContDiffOn ℝ ∞ (fun t ↦ (F.connection t).scalarCurvature x) J := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have h := F.contMDiffOn_scalarCurvature.comp hslice.contMDiffOn
    (show Set.MapsTo (fun t : ℝ ↦ (t, x)) J (J ×ˢ Set.univ) from
      fun _ ht ↦ ⟨ht, Set.mem_univ x⟩)
  exact h.contDiffOn


theorem scalarCurvature_timeDerivative_extend (x : M) (v : ℝ → ℝ)
    (hv : ContinuousOn v J)
    (hi : ∀ t ∈ interior J,
      HasDerivAt (fun s ↦ (F.connection s).scalarCurvature x) (v t) t) :
    ∀ t ∈ J, HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) (v t) J t := by
  let f := fun t ↦ (F.connection t).scalarCurvature x
  have hf : ContDiffOn ℝ ∞ f J := F.contDiffOn_scalarCurvature_timeSlice x
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty := hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconv hne
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hinside : Set.EqOn (derivWithin f J) v (interior J) := by
    intro t ht
    exact (hi t ht).hasDerivWithinAt.derivWithin (hJ t (interior_subset ht))
  have heq : Set.EqOn (derivWithin f J) v J := hinside.of_subset_closure
    (hf.continuousOn_derivWithin hJ (by simp)) hv interior_subset hdense
  intro t ht
  exact ((hf t ht).differentiableWithinAt (by simp)).hasDerivWithinAt.congr_deriv (heq ht)

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in

theorem hasDerivWithinAt_scalarCurvature (t : ℝ) (ht : t ∈ J) (x : M) :
    HasDerivWithinAt (fun s : ℝ ↦ (F.connection s).scalarCurvature x)
      ((F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x) J t := by
  have hc : ContinuousOn
      (fun p : ℝ × M ↦ (F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
        2 * (F.connection p.1).ricciNormSq p.2) (J ×ˢ Set.univ) :=
    (M04.continuousOn_flow_timeDependentLaplacian F
      (q := fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2)
      F.contMDiffOn_scalarCurvature).add
      (continuousOn_const.mul (M04.continuousOn_flow_ricciNormSq F))
  have hv : ContinuousOn
      (fun s : ℝ ↦ (F.connection s).laplacian (F.connection s).scalarCurvature x +
        2 * (F.connection s).ricciNormSq x) J :=
    hc.comp (f := fun s : ℝ ↦ (s, x))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs ↦ ⟨hs, Set.mem_univ x⟩)
  exact F.scalarCurvature_timeDerivative_extend x _ hv
    (fun s hs ↦ M04.hasDerivAt_scalarCurvature_evolution (t := s) F hs x) t ht

end PoincareConjecture.RicciFlow

