import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusClosedConformality
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackConnection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m64Annulus_pushforward_contMDiffAt
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : ContMDiffAt (𝓡 2) (𝓡 n) ∞ f p) (v : LoopPlane) :
    ContMDiffAt (𝓡 2) ((𝓡 n).prod (𝓡 n)) ∞
      (fun q => (⟨f q, mfderiv (𝓡 2) (𝓡 n) f q v⟩ : TangentBundle (𝓡 n) M)) p := by
  have hv : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q : LoopPlane => (⟨q, v⟩ : TangentBundle (𝓡 2) LoopPlane)) p := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  exact (hf.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hv hf

omit [IsManifold (𝓡 n) ∞ M] in



theorem m64Annulus_horizontal_velocity
    {f : LoopPlane → M} {x s : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (annulusPoint x s)) :
    curveVelocity (fun y => f (annulusPoint y s)) x =
      mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) := by
  have hline := m64AnnulusPoint_horizontal_hasDerivAt s x
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
      (fun y => annulusPoint y s) x := hline.differentiableAt.mdifferentiableAt
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun y => annulusPoint y s) x 1 =
      EuclideanSpace.single (0 : Fin 2) 1 := by
    rw [mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hchain := mfderiv_comp_apply x hf hmd (1 : ℝ)
  rw [hd] at hchain
  exact hchain

omit [IsManifold (𝓡 n) ∞ M] in



theorem m64Annulus_vertical_velocity
    {f : LoopPlane → M} {x s : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (annulusPoint x s)) :
    curveVelocity (fun t => f (annulusPoint x t)) s =
      mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) := by
  have hline := m64AnnulusPoint_vertical_hasDerivAt x s
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) (annulusPoint x) s :=
    hline.differentiableAt.mdifferentiableAt
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (annulusPoint x) s 1 =
      EuclideanSpace.single (1 : Fin 2) 1 := by
    rw [mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hchain := mfderiv_comp_apply s hf hmd (1 : ℝ)
  rw [hd] at hchain
  exact hchain





theorem m64Annulus_horizontal_velocity_contMDiffAt
    {f : LoopPlane → M} {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O) {q : ℝ × ℝ}
    (hq : annulusPoint q.1 q.2 ∈ O) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ => (⟨f (annulusPoint z.1 z.2),
        curveVelocity (fun y => f (annulusPoint y z.2)) z.1⟩ :
          TangentBundle (𝓡 n) M)) q := by
  have hP : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (fun z : ℝ × ℝ => annulusPoint z.1 z.2) := by
    apply contMDiff_iff_contDiff.mpr
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  have h := (m64Annulus_pushforward_contMDiffAt (hf.contMDiffAt (hO.mem_nhds hq))
    (EuclideanSpace.single (0 : Fin 2) 1)).comp q (hP q)
  apply h.congr_of_eventuallyEq
  filter_upwards [(hP q).continuousAt (hO.mem_nhds hq)] with z hz
  congr 1
  exact m64Annulus_horizontal_velocity
    ((hf.contMDiffAt (hO.mem_nhds hz)).mdifferentiableAt (by simp))





theorem m64Annulus_vertical_velocity_contMDiffAt
    {f : LoopPlane → M} {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O) {q : ℝ × ℝ}
    (hq : annulusPoint q.1 q.2 ∈ O) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ => (⟨f (annulusPoint z.1 z.2),
        curveVelocity (fun t => f (annulusPoint z.1 t)) z.2⟩ :
          TangentBundle (𝓡 n) M)) q := by
  have hP : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (fun z : ℝ × ℝ => annulusPoint z.1 z.2) := by
    apply contMDiff_iff_contDiff.mpr
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  have h := (m64Annulus_pushforward_contMDiffAt (hf.contMDiffAt (hO.mem_nhds hq))
    (EuclideanSpace.single (1 : Fin 2) 1)).comp q (hP q)
  apply h.congr_of_eventuallyEq
  filter_upwards [(hP q).continuousAt (hO.mem_nhds hq)] with z hz
  congr 1
  exact m64Annulus_vertical_velocity
    ((hf.contMDiffAt (hO.mem_nhds hz)).mdifferentiableAt (by simp))

end PoincareConjecture
