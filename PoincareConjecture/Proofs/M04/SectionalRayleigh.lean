import PoincareConjecture.Proofs.M04.TensorEvolution
import PoincareConjecture.Proofs.M04.FlowRiemannRegularity
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Inv








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

noncomputable def metricGram (g : RiemannianMetric n M) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2

noncomputable def metricGramEvaluation (g : RiemannianMetric n M) :
    CovariantTensorEvaluation n M 4 := fun x v ↦
  g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3) -
    g.inner x (v 0) (v 3) * g.inner x (v 1) (v 2)

theorem isSmoothCovariantTensor_metricGramEvaluation (g : RiemannianMetric n M) :
    IsSmoothCovariantTensor (metricGramEvaluation g) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  · intro x
    refine ⟨MultilinearMap.mk' (R := ℝ) (metricGramEvaluation g x) ?_ ?_, fun _ ↦ rfl⟩
    · intro v i a b
      fin_cases i <;>
        simp [metricGramEvaluation, Function.update, map_add, add_apply] <;> ring
    · intro v i r a
      fin_cases i <;>
        simp [metricGramEvaluation, Function.update, map_smul, smul_apply, smul_eq_mul] <;> ring
  · intro U hU X hX
    exact ((hX 0).inner_bundle (hX 2) |>.mul ((hX 1).inner_bundle (hX 3))).sub
      ((hX 0).inner_bundle (hX 3) |>.mul ((hX 1).inner_bundle (hX 2)))

theorem metricGram_pos_of_linearIndependent (g : RiemannianMetric n M) (x : M)
    (u v : TangentSpace (𝓡 n) x) (hlin : LinearIndependent ℝ ![u, v]) :
    0 < metricGram g x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := (Matrix.posDef_gram_of_linearIndependent hlin).det_pos
  have hinner (a b : TangentSpace (𝓡 n) x) : inner ℝ a b = g.inner x a b := rfl
  simpa only [Matrix.det_fin_two, Matrix.gram, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, hinner, g.symm x v u, ← pow_two, metricGram] using h

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_sectionalRayleigh
    (F : RicciFlow n M J) (t : ℝ) (ht : t ∈ J)
    (x : M) (u v : TangentSpace (𝓡 n) x)
    (hgram : 0 < metricGram (F.metric t) x u v) :
    HasDerivWithinAt
      (fun s ↦ (F.connection s).curvatureTensor x u v u v /
        metricGram (F.metric s) x u v)
      (((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, u, v] + (F.connection t).curvatureReaction x u v u v) /
        metricGram (F.metric t) x u v -
        (F.connection t).curvatureTensor x u v u v *
          (-2 * (F.connection t).ricci x u u * (F.metric t).inner x v v -
            2 * (F.metric t).inner x u u * (F.connection t).ricci x v v +
            4 * (F.connection t).ricci x u v * (F.metric t).inner x u v) /
          (metricGram (F.metric t) x u v) ^ 2) J t := by
  have hg : HasDerivWithinAt (fun s ↦ metricGram (F.metric s) x u v)
      (-2 * (F.connection t).ricci x u u * (F.metric t).inner x v v -
        2 * (F.metric t).inner x u u * (F.connection t).ricci x v v +
        4 * (F.connection t).ricci x u v * (F.metric t).inner x u v) J t := by
    have h := ((F.equation t ht x u u).mul (F.equation t ht x v v)).sub
      ((F.equation t ht x u v).pow 2)
    convert! h using 1
    ring
  have h := (F.hasDerivWithinAt_curvatureTensor t ht x u v u v).div hg hgram.ne'
  convert! h using 1
  field_simp

def modelOrthonormalPairs (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ inner ℝ p.1 p.2 = 0}

theorem isCompact_modelOrthonormalPairs (n : ℕ) :
    IsCompact (modelOrthonormalPairs n) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hclosed : IsClosed (modelOrthonormalPairs n) :=
    (isClosed_eq continuous_fst.norm continuous_const).inter
      ((isClosed_eq continuous_snd.norm continuous_const).inter
        (isClosed_eq (continuous_fst.inner continuous_snd) continuous_const))
  apply ((isCompact_sphere (0 : E) 1).prod (isCompact_sphere (0 : E) 1)).of_isClosed_subset
    hclosed
  intro p hp
  exact ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hp.1,
    by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2.1⟩


set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_sectionalRayleigh_trivialization
    (F : RicciFlow n M J) (c : M) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
    ContinuousOn (fun p : (ℝ × M) × (E × E) ↦
      (F.connection p.1.1).curvatureTensor p.1.2
          (e.symmL ℝ p.1.2 p.2.1) (e.symmL ℝ p.1.2 p.2.2)
          (e.symmL ℝ p.1.2 p.2.1) (e.symmL ℝ p.1.2 p.2.2) /
        metricGram (F.metric p.1.1) p.1.2
          (e.symmL ℝ p.1.2 p.2.1) (e.symmL ℝ p.1.2 p.2.2))
      ((J ×ˢ e.baseSet) ×ˢ modelOrthonormalPairs n) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  let S := fun y ↦ e.symmL ℝ y
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let W := J ×ˢ e.baseSet
  let V := W ×ˢ modelOrthonormalPairs n
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
  let R (a : Fin 4 → Fin n) : ℝ × M → ℝ := fun p ↦
    (F.connection p.1).riemannEvaluation p.2 (fun j ↦ S p.2 (b (a j)))
  have hR (a : Fin 4 → Fin n) : ContinuousOn (R a) W :=
    (contMDiffOn_flow_riemannEvaluation F e.open_baseSet
      (fun j y ↦ S y (b (a j))) (fun j ↦ hS (b (a j)))).continuousOn
  let v : (ℝ × M) × (E × E) → Fin 4 → E :=
    fun p ↦ ![p.2.1, p.2.2, p.2.1, p.2.2]
  have hv (j : Fin 4) : Continuous (fun p : (ℝ × M) × (E × E) ↦ v p j) := by
    fin_cases j
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd
  have hExpand (p : (ℝ × M) × (E × E)) :
      (F.connection p.1.1).riemannEvaluation p.1.2 (fun j ↦ S p.1.2 (v p j)) =
        ∑ a : Fin 4 → Fin n, (∏ j, inner ℝ (b (a j)) (v p j)) * R a p.1 := by
    obtain ⟨A, hA⟩ := (isSmoothCovariantTensor_riemannEvaluation (F.connection p.1.1)).1 p.1.2
    have hrec (w : E) : (∑ i, inner ℝ (b i) w • S p.1.2 (b i)) = S p.1.2 w := by
      calc
        _ = S p.1.2 (∑ i, inner ℝ (b i) w • b i) := by simp only [map_sum, map_smul]
        _ = S p.1.2 w := congrArg (S p.1.2) (b.sum_repr' w)
    rw [hA]
    calc
      A (fun j ↦ S p.1.2 (v p j)) =
          A (fun j ↦ ∑ i, inner ℝ (b i) (v p j) • S p.1.2 (b i)) := by
            simp only [hrec]
      _ = ∑ a : Fin 4 → Fin n,
          A (fun j ↦ inner ℝ (b (a j)) (v p j) • S p.1.2 (b (a j))) := A.map_sum _
      _ = _ := by simp only [A.map_smul_univ, smul_eq_mul, R, hA]
  have hRP : ContinuousOn (fun p : (ℝ × M) × (E × E) ↦
      (F.connection p.1.1).curvatureTensor p.1.2
        (S p.1.2 p.2.1) (S p.1.2 p.2.2) (S p.1.2 p.2.1) (S p.1.2 p.2.2)) V := by
    have hs : ContinuousOn (fun p : (ℝ × M) × (E × E) ↦
        ∑ a : Fin 4 → Fin n, (∏ j, inner ℝ (b (a j)) (v p j)) * R a p.1) V := by
      apply continuousOn_finsetSum
      intro a ha
      apply ContinuousOn.mul
      · apply continuousOn_finsetProd
        intro j hj
        exact (continuous_const.inner (hv j)).continuousOn
      · exact (hR a).comp continuousOn_fst (fun _ hp ↦ hp.1)
    apply hs.congr
    intro p hp
    exact hExpand p
  let G : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2).bilinearComp (S p.2) (S p.2)
  have hG : ContinuousOn G W := by
    apply continuousOn_clm_apply.mpr
    intro a
    apply continuousOn_clm_apply.mpr
    intro d
    have hSa : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' E p.2 (S p.2 a)) W :=
      (hS a).comp contMDiffOn_snd
        (show MapsTo (Prod.snd : ℝ × M → M) W e.baseSet from fun _ hp ↦ hp.2)
    have hSd : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' E p.2 (S p.2 d)) W :=
      (hS d).comp contMDiffOn_snd
        (show MapsTo (Prod.snd : ℝ × M → M) W e.baseSet from fun _ hp ↦ hp.2)
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ G p a d) W := by
      intro p hp
      have hm := (F.smooth p ⟨hp.1, mem_univ p.2⟩).mono
        (show W ⊆ J ×ˢ univ from fun q hq ↦ ⟨hq.1, mem_univ q.2⟩)
      have he : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
          (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
            (G q a d)) W p :=
        hm.clm_bundle_apply₂ (hSa p hp) (hSd p hp)
      simp only [Bundle.contMDiffWithinAt_totalSpace] at he
      exact he.2
    exact hg.continuousOn
  have hGP (a d : (ℝ × M) × (E × E) → E) (ha : Continuous a) (hd : Continuous d) :
      ContinuousOn (fun p : (ℝ × M) × (E × E) ↦ G p.1 (a p) (d p)) V :=
    ((hG.comp continuousOn_fst (fun _ hp ↦ hp.1)).clm_apply ha.continuousOn).clm_apply
      hd.continuousOn
  have hfst : Continuous (fun p : (ℝ × M) × (E × E) ↦ p.2.1) :=
    continuous_fst.comp continuous_snd
  have hsnd : Continuous (fun p : (ℝ × M) × (E × E) ↦ p.2.2) :=
    continuous_snd.comp continuous_snd
  have hH : ContinuousOn (fun p : (ℝ × M) × (E × E) ↦
      metricGram (F.metric p.1.1) p.1.2 (S p.1.2 p.2.1) (S p.1.2 p.2.2)) V :=
    ((hGP _ _ hfst hfst).mul (hGP _ _ hsnd hsnd)).sub ((hGP _ _ hfst hsnd).pow 2)
  apply hRP.div hH
  intro p hp
  apply ne_of_gt (metricGram_pos_of_linearIndependent (F.metric p.1.1) p.1.2
    (S p.1.2 p.2.1) (S p.1.2 p.2.2) ?_)
  have horth : Orthonormal ℝ (![p.2.1, p.2.2] : Fin 2 → E) := by
    constructor
    · intro i
      fin_cases i
      · exact hp.2.1
      · exact hp.2.2.1
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hp.2.2.2
      · change inner ℝ p.2.2 p.2.1 = 0
        rw [real_inner_comm]
        exact hp.2.2.2
      · exact (hij rfl).elim
  have hinj : Function.Injective (S p.1.2) := by
    intro a d had
    have h := congrArg (e.continuousLinearMapAt ℝ p.1.2) had
    simpa only [S, e.continuousLinearMapAt_symmL hp.1.2] using h
  have hl := horth.linearIndependent.map' (S p.1.2).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  convert! hl using 1
  funext i
  fin_cases i <;> rfl

end PoincareConjecture.M04


