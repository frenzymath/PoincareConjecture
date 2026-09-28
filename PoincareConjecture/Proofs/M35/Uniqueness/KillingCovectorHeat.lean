import PoincareConjecture.Proofs.M35.Uniqueness.KillingCovector
import PoincareConjecture.Proofs.M04.TensorTimeCommutator

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem killingCovector_heat_hasDerivAt
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ioo 0 G.lifetime)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ContDiff ℝ ∞ (X t)) (x : StandardCapSpace) (v : Fin 1 → StandardCapSpace)
    (hheat : HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t) :
    HasDerivAt (fun s => killingCovector (G.flow.metric s) (X s) x v)
      ((G.flow.connection t).tensorLaplacian (killingCovector (G.flow.metric t) (X t)) x v -
        (G.flow.connection t).ricci x (v 0) (X t x)) t := by
  have htJ : t ∈ Ico 0 G.lifetime := ⟨ht.1.le, ht.2⟩
  have huniq := uniqueDiffOn_Ico 0 G.lifetime t htJ
  have hd := movingMetric_hasDerivWithinAt_pair G.flow.smooth htJ huniq x hheat
    (hasDerivWithinAt_const t (Ico 0 G.lifetime) (v 0))
  have hg := G.flow.equation t htJ x (X t x) (v 0)
  rw [hg.derivWithin huniq, map_zero, add_zero] at hd
  have hpair : (G.flow.metric t).inner x
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (v 0) =
      (G.flow.connection t).tensorLaplacian (killingCovector (G.flow.metric t) (X t)) x v +
        (G.flow.connection t).ricci x (v 0) (X t x) := by
    rw [killingCovector_laplacian _ _ hX]
    calc
      _ = (G.flow.metric t).inner x (∑ i, fieldHessian (G.flow.connection t) (X t) x
            ((G.flow.metric t).orthonormalBasis x i)
            ((G.flow.metric t).orthonormalBasis x i)) (v 0) +
          (G.flow.metric t).inner x
            (RicciFlow.ricciSharp (G.flow.connection t) x (X t x)) (v 0) := by
        exact congrArg (fun L => L (v 0))
          (((G.flow.metric t).euclideanCoefficients x).map_add _ _)
      _ = _ := by rw [inner_ricciSharp]
  have htime : Ico 0 G.lifetime ∈ 𝓝 t :=
    mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Ico_self
  convert! hd.hasDerivAt htime using 1
  rw [hpair, DeTurckNative.intrinsicRicci_symm (G.flow.connection t) x (X t x) (v 0)]
  ring

theorem killingCovector_joint_flow {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (J ×ˢ univ))
    (U : Set StandardCapSpace) (_hU : IsOpen U)
    (Y : Fin 1 → StandardCapSpace → StandardCapSpace)
    (hY : ∀ i, ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun y => Bundle.TotalSpace.mk' StandardCapSpace y
        (E := TangentSpace (𝓡 3)) (Y i y)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × StandardCapSpace =>
        killingCovector (F.metric p.1) (X p.1) p.2 (fun i => Y i p.2))
      (J ×ˢ U) := by
  have hXU := hX.mono (prod_mono Subset.rfl (subset_univ U))
  have hYU := (hY 0).comp (I := 𝓘(ℝ, ℝ).prod (𝓡 3)) contMDiffOn_snd
    (fun (p : ℝ × StandardCapSpace) (hp : p ∈ J ×ˢ U) => hp.2)
  have hm := F.smooth.mono (prod_mono Subset.rfl (subset_univ U))
  have hpair := ContMDiffOn.clm_bundle_apply₂
    (F₁ := StandardCapSpace) (F₂ := StandardCapSpace) (F₃ := ℝ)
    (E₁ := TangentSpace (𝓡 3)) (E₂ := TangentSpace (𝓡 3))
    (E₃ := fun _ : StandardCapSpace => ℝ)
    (ψ := fun p : ℝ × StandardCapSpace => (F.metric p.1).inner p.2)
    (b := Prod.snd) hm hXU hYU
  intro p hp
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair p hp)).2

theorem killingCovector_joint
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ))
    (U : Set StandardCapSpace) (hU : IsOpen U)
    (Y : Fin 1 → StandardCapSpace → StandardCapSpace)
    (hY : ∀ i, ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
      (fun y => Bundle.TotalSpace.mk' StandardCapSpace y
        (E := TangentSpace (𝓡 3)) (Y i y)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × StandardCapSpace =>
        killingCovector (G.flow.metric p.1) (X p.1) p.2 (fun i => Y i p.2))
      (Ico 0 G.lifetime ×ˢ U) :=
  killingCovector_joint_flow G.flow X hX U hU Y hY

end PoincareConjecture.M35.Uniqueness
