import PoincareConjecture.Proofs.M04.TensorEvolution
import PoincareConjecture.Proofs.M04.FlowTensorRegularity
import Mathlib.Analysis.Calculus.Deriv.Inv





set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_ricciRayleigh
    (F : RicciFlow n M J) (t : ℝ) (ht : t ∈ J)
    (x : M) (u : TangentSpace (𝓡 n) x) (hu : u ≠ 0) :
    HasDerivWithinAt
      (fun s ↦ (F.connection s).ricci x u u / (F.metric s).inner x u u)
      (((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![u, u] +
          (F.connection t).ricciReaction x u u) / (F.metric t).inner x u u +
        2 * ((F.connection t).ricci x u u / (F.metric t).inner x u u) ^ 2) J t := by
  have hne : (F.metric t).inner x u u ≠ 0 := ne_of_gt ((F.metric t).pos x u hu)
  have hd := (F.hasDerivWithinAt_ricci t ht x u u).div (F.equation t ht x u u) hne
  convert! hd using 1
  field_simp
  ring

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_ricciRayleigh_trivialization
    (F : RicciFlow n M J) (c : M) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
    ContinuousOn (fun p : (ℝ × M) × E ↦
      (F.connection p.1.1).ricci p.1.2
          (e.symmL ℝ p.1.2 p.2) (e.symmL ℝ p.1.2 p.2) /
        (F.metric p.1.1).inner p.1.2
          (e.symmL ℝ p.1.2 p.2) (e.symmL ℝ p.1.2 p.2))
      ((J ×ˢ e.baseSet) ×ˢ {w : E | w ≠ 0}) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  let S := fun y ↦ e.symmL ℝ y
  have hc : c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' c
  have hSext (a : E) {y : M} (hy : y ∈ e.baseSet) :
      FiberBundle.extend E (S c a) y = S y a := by
    change e.symm y (e ⟨c, e.symmL ℝ c a⟩).2 = e.symmL ℝ y a
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hc,
      e.continuousLinearMapAt_symmL hc, e.symmL_apply hy]
  have hS (a : E) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (T% (fun y ↦ S y a)) e.baseSet := by
    apply (contMDiffOn_extend_baseSet (S c a)).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext a hy).symm
  choose A hA using fun p : ℝ × M ↦
    (isSmoothCovariantTensor_ricciEvaluation (F.connection p.1)).1 p.2
  have hu0 {y : M} (a b d : TangentSpace (𝓡 n) y) :
      Function.update ![a, b] 0 d = ![d, b] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu1 {y : M} (a b d : TangentSpace (𝓡 n) y) :
      Function.update ![a, b] 1 d = ![a, d] := by
    funext i
    fin_cases i <;> simp [Function.update]
  let L : ℝ × M → E →ₗ[ℝ] E →L[ℝ] ℝ := fun p ↦
    { toFun := fun a ↦
        (((A p).toLinearMap ![S p.2 a, 0] 1).comp (S p.2).toLinearMap).toContinuousLinearMap
      map_add' := by
        intro a b
        ext d
        simp only [add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, hu1]
        change A p ![S p.2 (a + b), S p.2 d] =
          A p ![S p.2 a, S p.2 d] + A p ![S p.2 b, S p.2 d]
        rw [map_add]
        simpa only [hu0] using (A p).map_update_add ![0, S p.2 d] 0 (S p.2 a) (S p.2 b)
      map_smul' := by
        intro r a
        ext b
        simp only [smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, hu1, RingHom.id_apply]
        change A p ![S p.2 (r • a), S p.2 b] = r • A p ![S p.2 a, S p.2 b]
        rw [map_smul]
        simpa only [hu0] using (A p).map_update_smul ![0, S p.2 b] 0 r (S p.2 a) }
  let B : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦ (L p).toContinuousLinearMap
  have hBval (p : ℝ × M) (a b : E) :
      B p a b = (F.connection p.1).ricci p.2 (S p.2 a) (S p.2 b) := by
    change A p (Function.update ![S p.2 a, 0] 1 (S p.2 b)) = _
    rw [hu1]
    exact (hA p ![S p.2 a, S p.2 b]).symm
  have hR (a b : E) :
      ContinuousOn (fun p : ℝ × M ↦
        (F.connection p.1).ricci p.2 (S p.2 a) (S p.2 b)) (J ×ˢ e.baseSet) := by
    have hX : ∀ i : Fin 2, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (T% ((![fun y ↦ S y a, fun y ↦ S y b] :
          Fin 2 → (y : M) → TangentSpace (𝓡 n) y) i)) e.baseSet := by
      intro i
      fin_cases i
      · exact hS a
      · exact hS b
    exact (contMDiffOn_flow_ricciEvaluation F e.open_baseSet hX).continuousOn
  have hB : ContinuousOn B (J ×ˢ e.baseSet) := by
    apply continuousOn_clm_apply.mpr
    intro a
    apply continuousOn_clm_apply.mpr
    intro b
    simpa only [hBval] using hR a b
  let G : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2).bilinearComp (S p.2) (S p.2)
  have hG : ContinuousOn G (J ×ˢ e.baseSet) := by
    apply continuousOn_clm_apply.mpr
    intro a
    apply continuousOn_clm_apply.mpr
    intro b
    have hSa : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' E p.2 (S p.2 a)) (J ×ˢ e.baseSet) :=
      (hS a).comp contMDiffOn_snd
      (show MapsTo (Prod.snd : ℝ × M → M) (J ×ˢ e.baseSet) e.baseSet from fun _ hp ↦ hp.2)
    have hSb : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' E p.2 (S p.2 b)) (J ×ˢ e.baseSet) :=
      (hS b).comp contMDiffOn_snd
      (show MapsTo (Prod.snd : ℝ × M → M) (J ×ˢ e.baseSet) e.baseSet from fun _ hp ↦ hp.2)
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ G p a b) (J ×ˢ e.baseSet) := by
      intro p hp
      have hm := (F.smooth p ⟨hp.1, mem_univ p.2⟩).mono
        (show J ×ˢ e.baseSet ⊆ J ×ˢ univ from fun q hq ↦ ⟨hq.1, mem_univ q.2⟩)
      have he : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
          (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
            (G q a b)) (J ×ˢ e.baseSet) p :=
        hm.clm_bundle_apply₂ (hSa p hp) (hSb p hp)
      simp only [Bundle.contMDiffWithinAt_totalSpace] at he
      exact he.2
    exact hg.continuousOn
  let V := (J ×ˢ e.baseSet) ×ˢ {w : E | w ≠ 0}
  have hBP : ContinuousOn (fun p : (ℝ × M) × E ↦ B p.1 p.2 p.2) V :=
    ((hB.comp continuousOn_fst (fun _ hp ↦ hp.1)).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd
  have hGP : ContinuousOn (fun p : (ℝ × M) × E ↦ G p.1 p.2 p.2) V :=
    ((hG.comp continuousOn_fst (fun _ hp ↦ hp.1)).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd
  have hGne (p : (ℝ × M) × E) (hp : p ∈ V) : G p.1 p.2 p.2 ≠ 0 := by
    apply ne_of_gt ((F.metric p.1.1).pos p.1.2 (S p.1.2 p.2) ?_)
    intro hz
    have hw := congrArg (e.continuousLinearMapAt ℝ p.1.2) hz
    have he : p.2 = 0 := by
      simpa only [S, e.continuousLinearMapAt_symmL hp.1.2, map_zero] using hw
    exact hp.2 he
  apply (hBP.div hGP hGne).congr
  intro p hp
  change (F.connection p.1.1).ricci p.1.2 (S p.1.2 p.2) (S p.1.2 p.2) /
    (F.metric p.1.1).inner p.1.2 (S p.1.2 p.2) (S p.1.2 p.2) =
      B p.1 p.2 p.2 / G p.1 p.2 p.2
  rw [hBval]
  rfl

end PoincareConjecture.M04

