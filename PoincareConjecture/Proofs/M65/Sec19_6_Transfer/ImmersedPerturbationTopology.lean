import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationVelocity
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.LoopTopology











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {V : Set P} {J : Set ℝ}




theorem loop_family_continuousOn
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (hV : IsOpen V) (hJ : IsOpen J)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (V ×ˢ (univ ×ˢ J))) :
    ContinuousOn (fun z : P × ℝ => Gamma z.1 z.2) (V ×ˢ J) := by
  have hU : IsOpen (V ×ˢ (univ ×ˢ J) : Set (P × (ℝ × ℝ))) :=
    hV.prod (isOpen_univ.prod hJ)
  have hphase := angular_velocity_contMDiffOn _ _ hU hGamma
  have hmap : Continuous (fun z : (P × ℝ) × ℝ => (z.1.1, (z.2, z.1.2))) :=
    continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply m65C1Loop_tendsto_of_angular _ (Gamma z.1 z.2)
  · intro x
    rw [← nhds_prod_eq]
    exact (hGamma.continuousOn.continuousAt (hU.mem_nhds
      ⟨hz.1, mem_univ _, hz.2⟩)).comp hmap.continuousAt
  · intro x
    rw [← nhds_prod_eq]
    exact (hphase.continuousOn.continuousAt (hU.mem_nhds
      ⟨hz.1, mem_univ _, hz.2⟩)).comp hmap.continuousAt






theorem loop_tendsto_of_parameter
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (hV : IsOpen V) (hJ : IsOpen J)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (V ×ˢ (univ ×ˢ J)))
    {ι : Type*} {l : Filter ι} (p : ι → P) (p0 : P) (hp0 : p0 ∈ V)
    (hp : Tendsto p l (𝓝 p0)) (q : ℝ) (hq : q ∈ J)
    (gamma : C1FreeLoopSpace (M := M))
    (hbase : ∀ x, periodicFreeLoop (Gamma p0 q) x = periodicFreeLoop gamma x) :
    Tendsto (fun i => Gamma (p i) q) l (𝓝 gamma) := by
  have hU : IsOpen (V ×ˢ (univ ×ˢ J) : Set (P × (ℝ × ℝ))) :=
    hV.prod (isOpen_univ.prod hJ)
  have hphase := angular_velocity_contMDiffOn _ _ hU hGamma
  have hmap (x : ℝ) : Tendsto (fun z : ι × ℝ => (p z.1, (z.2, q)))
      (l ×ˢ 𝓝 x) (𝓝 (p0, (x, q))) :=
    (hp.comp tendsto_fst).prodMk_nhds (tendsto_snd.prodMk_nhds tendsto_const_nhds)
  apply m65C1Loop_tendsto_of_angular _ gamma
  · intro x
    have h := (hGamma.continuousOn.continuousAt (hU.mem_nhds
      ⟨hp0, mem_univ _, hq⟩)).tendsto.comp (hmap x)
    simpa +instances only [Function.comp_def, hbase x] using! h
  · intro x
    have h := (hphase.continuousOn.continuousAt (hU.mem_nhds
      ⟨hp0, mem_univ _, hq⟩)).tendsto.comp (hmap x)
    have he : (⟨periodicFreeLoop (Gamma p0 q) x,
        curveVelocity (n := 3) (periodicFreeLoop (Gamma p0 q)) x⟩ :
          TangentBundle (𝓡 3) M) =
        (⟨periodicFreeLoop gamma x, curveVelocity (n := 3) (periodicFreeLoop gamma) x⟩ :
          TangentBundle (𝓡 3) M) :=
      congrArg (fun f : ℝ → M => (⟨f x, curveVelocity (n := 3) f x⟩ :
        TangentBundle (𝓡 3) M)) (funext hbase)
    simpa +instances only [Function.comp_def, he] using! h

end PoincareConjecture.M65Perturbation
