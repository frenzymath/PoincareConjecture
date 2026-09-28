import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarMollifiedCutoff
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AreaMeasurability
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64Uniformization

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)





theorem scalarC1_composed_gram_tendsto
    (g : RiemannianMetric n M) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) 1 f U)
    {u : Plane → E} {v : ℕ → Plane → E} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : ∀ j, DifferentiableAt ℝ (v j) x)
    (huU : u x ∈ U) (hvU : ∀ j, v j x ∈ U)
    (hval : Tendsto (fun j => v j x) atTop (𝓝 (u x)))
    (hcol : ∀ i : Fin 2, Tendsto
      (fun j => fderiv ℝ (v j) x (EuclideanSpace.single i 1)) atTop
      (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1)))) (i k : Fin 2) :
    Tendsto (fun j => m60AreaGram g (f ∘ v j) x i k) atTop
      (𝓝 (m60AreaGram g (f ∘ u) x i k)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let B := fun p : E × (E × E) =>
    g.inner (f p.1) (mfderiv (𝓡 m) (𝓡 n) f p.1 p.2.1)
      (mfderiv (𝓡 m) (𝓡 n) f p.1 p.2.2)
  have hB : ContinuousOn B (U ×ˢ univ) := M60.continuousOn_pullback_inner hU hf
  have hb := (hB.continuousAt ((hU.prod isOpen_univ).mem_nhds
    (show (u x, fderiv ℝ u x (EuclideanSpace.single i 1),
      fderiv ℝ u x (EuclideanSpace.single k 1)) ∈ U ×ˢ univ from ⟨huU, mem_univ _⟩))).tendsto
  have hlim := hb.comp (hval.prodMk_nhds ((hcol i).prodMk_nhds (hcol k)))
  have heq (w : Plane → E) (hw : DifferentiableAt ℝ w x) (hwU : w x ∈ U) :
      m60AreaGram g (f ∘ w) x i k =
        B (w x, fderiv ℝ w x (EuclideanSpace.single i 1),
          fderiv ℝ w x (EuclideanSpace.single k 1)) := by
    have hfd := (hf.contMDiffAt (hU.mem_nhds hwU)).mdifferentiableAt one_ne_zero
    simp only [m60AreaGram, mfderiv_comp x hfd
      (mdifferentiableAt_iff_differentiableAt.mpr hw), mfderiv_eq_fderiv,
      EuclideanSpace.basisFun_apply, ContinuousLinearMap.comp_apply, B,
      Function.comp_apply]
    rfl
  have heqv : (fun j => m60AreaGram g (f ∘ v j) x i k) =
      B ∘ (fun j => (v j x, fderiv ℝ (v j) x (EuclideanSpace.single i 1),
        fderiv ℝ (v j) x (EuclideanSpace.single k 1))) :=
    funext fun j => heq (v j) (hv j) (hvU j)
  rw [heqv, heq u hu huU]
  exact hlim




theorem scalarC1_composed_area_tendsto
    (g : RiemannianMetric n M) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 m) (𝓡 n) 1 f U)
    {u : Plane → E} {v : ℕ → Plane → E} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : ∀ j, DifferentiableAt ℝ (v j) x)
    (huU : u x ∈ U) (hvU : ∀ j, v j x ∈ U)
    (hval : Tendsto (fun j => v j x) atTop (𝓝 (u x)))
    (hcol : ∀ i : Fin 2, Tendsto
      (fun j => fderiv ℝ (v j) x (EuclideanSpace.single i 1)) atTop
      (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1)))) :
    Tendsto (fun j => m60AreaDensity g (f ∘ v j) x) atTop
      (𝓝 (m60AreaDensity g (f ∘ u) x)) := by
  have hg := scalarC1_composed_gram_tendsto g hU hf hu hv huU hvU hval hcol
  have hd := ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  simpa only [m60AreaDensity, Matrix.det_fin_two] using
    ((show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds).max hd).sqrt

end PoincareConjecture.M64Uniformization
