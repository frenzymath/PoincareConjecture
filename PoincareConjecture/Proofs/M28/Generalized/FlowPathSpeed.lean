import PoincareConjecture.Proofs.M08.ReferenceEnergy
import PoincareConjecture.Proofs.M28.Generalized.BoxTransport












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture




theorem RicciFlow.continuousOn_tangentNorm_curveVelocity
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J I : Set ℝ} (G : RicciFlow n M J) {γ : ℝ → M}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ I) :
    ContinuousOn (fun z : ℝ × ℝ =>
      (G.metric z.1).tangentNorm (γ z.2) (curveVelocity γ z.2)) (J ×ˢ I) := by
  have hbase : ContinuousOn (fun z : ℝ × ℝ => (z.1, γ z.2)) (J ×ˢ I) :=
    continuous_fst.continuousOn.prodMk
      (hγ.continuousOn.comp continuous_snd.continuousOn fun _ hz => hz.2)
  have hg := G.smooth.continuousOn.comp hbase (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have hv : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨γ z.2, curveVelocity γ z.2⟩ : TangentBundle (𝓡 n) M)) (J ×ˢ I) :=
    (M08.curveVelocity_continuousOn_open hI hγ).comp
      continuous_snd.continuousOn (fun _ hz => hz.2)
  have heval : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨γ z.2, (G.metric z.1).inner (γ z.2)
        (curveVelocity γ z.2) (curveVelocity γ z.2)⟩ :
        Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ))) (J ×ˢ I) :=
    hg.clm_bundle_apply₂ hv hv
  exact Real.continuous_sqrt.comp_continuousOn
    (((Bundle.Trivial.homeomorphProd M ℝ).continuous.comp_continuousOn heval).snd)




theorem GeneralizedRicciFlowData.tangentNorm_box_curve
    (F : GeneralizedRicciFlowData.{u}) (b : F.box_index)
    (s : ℝ) (hs : s ∈ (F.box b).interval)
    (γ : ℝ → (F.box b).carrier.carrier) (v : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ) (𝓡 3) γ v) :
    (F.metric s).tangentNorm ((F.box b).forward s hs (γ v))
        (curveVelocity ((F.box b).forward s hs ∘ γ) v) =
      ((F.box b).flow.metric s).tangentNorm (γ v) (curveVelocity γ v) := by
  unfold RiemannianMetric.tangentNorm curveVelocity
  rw [mfderiv_comp v (((F.box b).forward_smooth s hs).mdifferentiable
    (by norm_num) (γ v)) hγ]
  exact congrArg Real.sqrt ((F.box b).metric_pullback s hs (γ v) _ _)

end PoincareConjecture
